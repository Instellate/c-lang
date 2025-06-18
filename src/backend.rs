use crate::ast::{
    Ast, Constant, ElseStatement, Expression, Function, FunctionArgType, FunctionArgument,
    FunctionCall, FunctionSignature, IfStatement, InfixOperator, VariableDeclaration,
};
use anyhow::{Result, anyhow};
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::llvm_sys::core::LLVMSetTailCall;
use inkwell::module::{Linkage, Module};
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine,
};
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::{
    AnyValue, AsValueRef, BasicValue, BasicValueEnum, FunctionValue, InstructionOpcode,
    PointerValue,
};
use inkwell::{AddressSpace, Either, IntPredicate, OptimizationLevel};
use llvm_sys::prelude::LLVMBool;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::path::Path;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum ReferenceType<'ctx> {
    Type(BasicTypeEnum<'ctx>),
    VariableValue(PointerValue<'ctx>, BasicTypeEnum<'ctx>),
    Value(BasicValueEnum<'ctx>),
    Function(FunctionValue<'ctx>),
    None,
}

impl<'ctx> ReferenceType<'ctx> {
    pub fn get_value(self, builder: &Builder<'ctx>) -> Result<BasicValueEnum<'ctx>> {
        match self {
            ReferenceType::VariableValue(v, t) => Ok(builder.build_load(t, v, "load-var")?),
            ReferenceType::Value(v) => Ok(v),
            _ => Err(anyhow!("Expected variable value or value")),
        }
    }
}

#[derive(Clone)]
pub struct IrBuilder<'ctx> {
    context: &'ctx Context,
    builder: Rc<Builder<'ctx>>,
    module: Rc<Module<'ctx>>,
    references: HashMap<String, ReferenceType<'ctx>>,
}

impl<'ctx> IrBuilder<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        Self {
            context,
            module: Rc::new(context.create_module("c-lang")),
            builder: Rc::new(context.create_builder()),
            references: Default::default(),
        }
    }
}

impl<'ctx> IrBuilder<'ctx> {
    pub fn visit_ast(&mut self, ast: Ast) -> Result<()> {
        match ast {
            Ast::FunctionSig(sig) => {
                self.visit_function_signature(sig)?;
            }
            Ast::Function(func) => {
                self.visit_function(func)?;
            }
            Ast::Expression(expr) => {
                self.visit_expression(expr)?;
            }
            _ => {}
        }

        Ok(())
    }

    pub fn visit_function_signature(
        &mut self,
        sig: FunctionSignature,
    ) -> Result<FunctionValue<'ctx>> {
        let mut args = vec![];
        let mut is_var_args = false;
        for arg in sig.arguments.iter() {
            match arg {
                FunctionArgType::Named(a) => args.push(self.visit_function_argument(a)?),
                FunctionArgType::VarArgs => is_var_args = true,
            }
        }
        let ReferenceType::Type(return_type) = self.visit_identifier(&sig.return_type)? else {
            return Err(anyhow!("Expected reference_type"));
        };

        let fn_type = return_type.fn_type(&args, is_var_args);

        let linkage = if sig.is_extern {
            Some(Linkage::External)
        } else {
            None
        };

        let fn_val = self.module.add_function(&sig.name, fn_type, linkage);
        for (i, arg) in sig.arguments.into_iter().enumerate() {
            if let FunctionArgType::Named(n) = arg {
                if let Some(p) = fn_val.get_nth_param(i as u32) {
                    p.set_name(&n.name)
                }
            }
        }

        self.references
            .insert(sig.name, ReferenceType::Function(fn_val));

        Ok(fn_val)
    }

    pub fn visit_function_argument(
        &self,
        argument: &FunctionArgument,
    ) -> Result<inkwell::types::BasicMetadataTypeEnum<'ctx>> {
        if argument.is_pointer {
            Ok(self.context.ptr_type(AddressSpace::from(0)).into())
        } else if let ReferenceType::Type(arg_type) = self.visit_identifier(&argument.arg_type)? {
            Ok(arg_type.into())
        } else {
            Err(anyhow!("Expected type"))
        }
    }

    pub fn visit_function(&mut self, function: Function) -> Result<()> {
        let args = function.signature.arguments.clone();
        let function_value = self.visit_function_signature(function.signature)?;

        for (i, arg) in args.into_iter().enumerate() {
            let FunctionArgType::Named(named) = arg else {
                continue;
            };
            let param = function_value
                .get_nth_param(i as u32)
                .ok_or_else(|| anyhow!("Expected param"))?;

            self.references
                .insert(named.name, ReferenceType::Value(param));
        }

        let mut self_clone = self.clone();
        self_clone.visit_block(
            function.block,
            self.context.append_basic_block(function_value, "entry"),
        )?;

        for block in function_value.get_basic_block_iter() {
            let returns = block
                .get_last_instruction()
                .map(|i| i.get_opcode() == InstructionOpcode::Return)
                .unwrap_or(false);

            if returns {
                let inst: Vec<inkwell::values::InstructionValue> =
                    block.get_instructions().collect();
                let mut rev = inst.into_iter().rev();
                rev.next().expect("Return instruction");

                for _ in 0..3 {
                    let Some(val) = rev.next() else {
                        break;
                    };

                    if val.get_opcode() == InstructionOpcode::Call {
                        unsafe { LLVMSetTailCall(val.as_value_ref(), LLVMBool::from(true)) }
                    }
                }
            }
        }

        Ok(())
    }

    pub fn visit_block(
        &mut self,
        ast_block: crate::ast::Block,
        block: BasicBlock<'ctx>,
    ) -> Result<BasicBlock<'ctx>> {
        self.builder.position_at_end(block);

        for ast in ast_block.into_iter() {
            match ast {
                Ast::VarDeclaration(v) => {
                    self.visit_variable_declaration(v)?;
                }
                Ast::Expression(e) => {
                    self.visit_expression(e)?;
                }
                Ast::Return(r) => self.visit_return(*r)?,
                Ast::Call(c) => {
                    self.visit_call(c)?;
                }
                Ast::IfStatement(i) => {
                    self.visit_if_statement(i)?;
                }
                _ => return Err(anyhow!("Expected statement or expression")),
            }
        }

        Ok(block)
    }

    pub fn visit_return(&mut self, ast: Ast) -> Result<()> {
        let value = match ast {
            Ast::Expression(expr) => self.visit_expression(expr)?,
            Ast::Constant(constant) => self.visit_constant(constant)?,
            Ast::Identifier(identifier) => self
                .visit_identifier(&identifier)?
                .get_value(&self.builder)?,
            Ast::Call(call) => self.visit_call(call)?,
            _ => {
                return Err(anyhow!(
                    "Expected expression, identifier, constant, or call"
                ));
            }
        };
        self.builder.build_return(Some(&value))?;

        Ok(())
    }

    pub fn visit_constant(&mut self, constant: Constant) -> Result<BasicValueEnum<'ctx>> {
        match constant {
            Constant::Integer(i) => Ok(self.context.i32_type().const_int(i as u64, false).into()),
            Constant::String(s) => Ok(self
                .builder
                .build_global_string_ptr(&s, "")?
                .as_basic_value_enum()),
        }
    }

    pub fn visit_variable_declaration(
        &mut self,
        variable_declaration: VariableDeclaration,
    ) -> Result<BasicValueEnum<'ctx>> {
        let ReferenceType::Type(var_type) =
            self.visit_identifier(&variable_declaration.var_type)?
        else {
            return Err(anyhow!("Expected type"));
        };

        let value = self
            .builder
            .build_alloca(var_type, &variable_declaration.name)?;
        self.references.insert(
            variable_declaration.name,
            ReferenceType::VariableValue(value, var_type),
        );

        Ok(value.into())
    }

    fn resolve_sides(&mut self, ast: Ast) -> Result<ReferenceType<'ctx>> {
        match ast {
            Ast::Expression(expr) => Ok(ReferenceType::Value(self.visit_expression(expr)?)),
            Ast::Constant(const_value) => {
                Ok(ReferenceType::Value(self.visit_constant(const_value)?))
            }
            Ast::Identifier(identifier) => self.visit_identifier(&identifier),
            Ast::VarDeclaration(v) => {
                self.visit_variable_declaration(v.clone())?;
                self.visit_identifier(&v.name)
            }
            _ => Err(anyhow!("Non supported value")),
        }
    }

    pub fn visit_expression(&mut self, expression: Expression) -> Result<BasicValueEnum<'ctx>> {
        let Expression::Infix(lhs, operator, rhs) = expression else {
            return Err(anyhow!("Expected infix"));
        };

        let lhs_val = self.resolve_sides(*lhs)?;
        let rhs_val = self.resolve_sides(*rhs)?;

        match operator {
            InfixOperator::Assignment => {
                let ReferenceType::VariableValue(value, _) = lhs_val.clone() else {
                    return Err(anyhow!("Expected variable"));
                };

                self.builder
                    .build_store(value, rhs_val.get_value(&self.builder)?)?;
                let val = lhs_val.get_value(&self.builder)?;
                Ok(val)
            }
            InfixOperator::Equals => Ok(self
                .builder
                .build_int_compare(
                    IntPredicate::EQ,
                    lhs_val.get_value(&self.builder)?.into_int_value(),
                    rhs_val.get_value(&self.builder)?.into_int_value(),
                    "cmp",
                )?
                .into()),
            InfixOperator::Mul => Ok(self
                .builder
                .build_int_mul(
                    lhs_val.get_value(&self.builder)?.into_int_value(),
                    rhs_val.get_value(&self.builder)?.into_int_value(),
                    "mul",
                )?
                .into()),
            InfixOperator::Div => Ok(self
                .builder
                .build_int_signed_div(
                    lhs_val.get_value(&self.builder)?.into_int_value(),
                    rhs_val.get_value(&self.builder)?.into_int_value(),
                    "signed-div",
                )?
                .into()),
            InfixOperator::Add => Ok(self
                .builder
                .build_int_add(
                    lhs_val.get_value(&self.builder)?.into_int_value(),
                    rhs_val.get_value(&self.builder)?.into_int_value(),
                    "add",
                )?
                .into()),
            InfixOperator::Sub => Ok(self
                .builder
                .build_int_sub(
                    lhs_val.get_value(&self.builder)?.into_int_value(),
                    rhs_val.get_value(&self.builder)?.into_int_value(),
                    "sub",
                )?
                .into()),
            InfixOperator::Modulo => Ok(self
                .builder
                .build_int_signed_rem(
                    lhs_val.get_value(&self.builder)?.into_int_value(),
                    rhs_val.get_value(&self.builder)?.into_int_value(),
                    "mod",
                )?
                .into()),
        }
    }

    pub fn visit_value(&mut self, ast: Ast) -> Result<BasicValueEnum<'ctx>> {
        match ast {
            Ast::Expression(e) => self.visit_expression(e),
            Ast::Identifier(i) => self.visit_identifier(&i)?.get_value(&self.builder),
            Ast::Constant(c) => self.visit_constant(c),
            Ast::Call(c) => self.visit_call(c),
            _ => Err(anyhow!("Expected value")),
        }
    }

    pub fn visit_call(&mut self, function_call: FunctionCall) -> Result<BasicValueEnum<'ctx>> {
        let ReferenceType::Function(function) = self.visit_identifier(&function_call.name)? else {
            return Err(anyhow!("Expected function"));
        };

        let mut values = vec![];
        for argument in function_call.arguments {
            values.push(self.visit_value(argument)?.into());
        }

        let call_value = self
            .builder
            .build_call(function, &values, "func-call")?
            .try_as_basic_value();

        Ok(match call_value {
            Either::Left(b) => b,
            Either::Right(_) => return Err(anyhow!("Expected basic value")),
        })
    }

    pub fn visit_if_statement(&mut self, statement: IfStatement) -> Result<BasicBlock<'ctx>> {
        let expression = self.visit_expression(statement.expression)?;
        let Some(current_block) = self.builder.get_insert_block() else {
            return Err(anyhow!("Expected some value for builder insert block"));
        };

        let if_block = self.context.insert_basic_block_after(current_block, "if");
        let mut self_cloned = self.clone();
        let if_block = self_cloned.visit_block(statement.block, if_block)?;

        let continue_block = self.context.insert_basic_block_after(if_block, "continue");

        let else_block = if let Some(else_statement) = statement.else_statement {
            let else_block = self.context.prepend_basic_block(continue_block, "else");

            let (else_block, returns_early) = match *else_statement {
                ElseStatement::Else(e) => {
                    let else_block = self.visit_block(e, else_block)?;

                    let ret = else_block
                        .get_instructions()
                        .find(|i| i.get_opcode() == InstructionOpcode::Return);
                    if ret.is_none() {
                        self.builder.build_unconditional_branch(continue_block)?;
                    }

                    self.builder.position_at_end(if_block);
                    (else_block, ret.is_some())
                }
                ElseStatement::ElseIf(ei) => {
                    self.builder.position_at_end(else_block);
                    let block = self.visit_if_statement(ei)?;
                    block.set_name("else-if");

                    let ret = block
                        .get_instructions()
                        .find(|i| i.get_opcode() == InstructionOpcode::Return);
                    if ret.is_none() {
                        self.builder.build_unconditional_branch(continue_block)?;
                    }
                    self.builder.position_at_end(if_block);

                    (else_block, ret.is_some())
                }
            };

            Some((else_block, returns_early))
        } else {
            None
        };

        self.builder.position_at_end(current_block);
        self.builder.build_conditional_branch(
            expression.into_int_value(),
            if_block,
            else_block.map(|(b, _)| b).unwrap_or_else(|| continue_block),
        )?;

        self.builder.position_at_end(if_block);
        let ret = if_block
            .get_instructions()
            .find(|i| i.get_opcode() == InstructionOpcode::Return);

        if ret.is_none() {
            self.builder.build_unconditional_branch(continue_block)?;
        }

        if let Some((_, returns_early)) = else_block {
            if returns_early {
                continue_block
                    .remove_from_function()
                    .map_err(|_| anyhow!("Couldn't remove from function"))?;
            } else {
                self.builder.build_unconditional_branch(continue_block)?;
            }
        }

        self.builder.position_at_end(continue_block);
        Ok(if_block)
    }

    fn visit_identifier(&self, name: &str) -> Result<ReferenceType<'ctx>> {
        match name {
            "int" => Ok(ReferenceType::Type(self.context.i32_type().into())),
            "char" => Ok(ReferenceType::Type(self.context.i8_type().into())),
            _ => Ok(self
                .references
                .get(name)
                .cloned()
                .unwrap_or(ReferenceType::None)),
        }
    }

    pub fn output_object(&self) -> Result<()> {
        let triple = TargetMachine::get_default_triple();
        let cpu = TargetMachine::get_host_cpu_name();
        let features = TargetMachine::get_host_cpu_features();

        let config = InitializationConfig::default();
        Target::initialize_all(&config);
        let target = Target::from_triple(&triple).map_err(|e| anyhow!(e.to_string()))?;
        let machine = target
            .create_target_machine(
                &triple,
                cpu.to_str()?,
                features.to_str()?,
                OptimizationLevel::Default,
                RelocMode::Default,
                CodeModel::Default,
            )
            .ok_or_else(|| anyhow!("Couldn't create host machine"))?;

        machine
            .write_to_file(&self.module, FileType::Object, Path::new("./ir.o"))
            .map_err(|e| anyhow!(e.to_string()))?;

        Ok(())
    }
}

impl Display for IrBuilder<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.module.to_string())
    }
}
