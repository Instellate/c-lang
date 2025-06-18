use crate::tokenizer::{Token, Tokenizer};
use anyhow::{Result, anyhow};

pub type Block = Vec<Ast>;

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum InfixOperator {
    Assignment,
    Equals,
    Mul,
    Div,
    Add,
    Sub,
    Modulo,
}

impl InfixOperator {
    pub fn precedence(&self) -> u16 {
        match self {
            Self::Mul | Self::Div | Self::Modulo => 2,
            Self::Add | Self::Sub => 3,
            Self::Equals => 4,
            Self::Assignment => 5,
        }
    }
}

impl TryFrom<&str> for InfixOperator {
    type Error = anyhow::Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "=" => Ok(Self::Assignment),
            "==" => Ok(Self::Equals),
            "*" => Ok(Self::Mul),
            "/" => Ok(Self::Div),
            "+" => Ok(Self::Add),
            "-" => Ok(Self::Sub),
            "%" => Ok(Self::Modulo),
            _ => Err(anyhow!("Operator does not exist")),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Constant {
    Integer(i64),
    String(String),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Expression {
    Prefix(InfixOperator, Box<Ast>),
    Infix(Box<Ast>, InfixOperator, Box<Ast>),
    Postfix(Box<Ast>, InfixOperator),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct VariableDeclaration {
    pub name: String,
    pub var_type: String,
}

impl VariableDeclaration {
    fn new(name: String, var_type: String) -> Self {
        Self { name, var_type }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FunctionSignature {
    pub name: String,
    pub return_type: String,
    pub arguments: Vec<FunctionArgType>,
    pub is_extern: bool,
}

impl FunctionSignature {
    pub fn new(
        name: String,
        return_type: String,
        arguments: Vec<FunctionArgType>,
        is_extern: bool,
    ) -> Self {
        Self {
            name,
            return_type,
            arguments,
            is_extern,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum FunctionArgType {
    Named(FunctionArgument),
    VarArgs,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FunctionArgument {
    pub name: String,
    pub arg_type: String,
    pub is_const: bool,
    pub is_pointer: bool,
}

impl FunctionArgument {
    pub fn new(name: String, arg_type: String, is_const: bool, is_pointer: bool) -> Self {
        Self {
            name,
            arg_type,
            is_const,
            is_pointer,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Function {
    pub signature: FunctionSignature,
    pub block: Block,
}

impl Function {
    pub fn new(signature: FunctionSignature, block: Block) -> Self {
        Self { signature, block }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FunctionCall {
    pub name: String,
    pub arguments: Vec<Ast>,
}

impl FunctionCall {
    pub fn new(name: String, arguments: Vec<Ast>) -> Self {
        Self { name, arguments }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ElseStatement {
    Else(Block),
    ElseIf(IfStatement),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct IfStatement {
    pub expression: Expression,
    pub block: Block,
    pub else_statement: Option<Box<ElseStatement>>,
}

impl IfStatement {
    pub fn new(
        expression: Expression,
        block: Block,
        else_statement: Option<Box<ElseStatement>>,
    ) -> Self {
        Self {
            expression,
            block,
            else_statement,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Type {
    Named(String),
    Pointer(Box<Type>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Ast {
    VarDeclaration(VariableDeclaration),
    Expression(Expression),
    Identifier(String),
    Type(Type),
    Constant(Constant),
    FunctionSig(FunctionSignature),
    Function(Function),
    Call(FunctionCall),
    Return(Box<Ast>),
    IfStatement(IfStatement),
    EOF,
}

impl Ast {
    pub fn is_expression(&self) -> bool {
        matches!(self, Self::Expression(_))
    }
}

pub struct Parser<'a> {
    tokenizer: Tokenizer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(tokenizer: Tokenizer<'a>) -> Self {
        Self { tokenizer }
    }

    fn parse_expression(&mut self, lhs: Ast, max_precedence: u16) -> Result<Ast> {
        let mut lhs = lhs;

        loop {
            let token = self.tokenizer.peek_token();
            let op_string = match token {
                Token::Operator(o) => o,
                _ => break,
            };

            let op = InfixOperator::try_from(op_string)?;
            let precedence = op.precedence();

            if precedence > max_precedence {
                break;
            }
            self.tokenizer.next_token();

            let rhs = {
                let ast = self.expr_parse_ast(true)?;
                self.parse_expression(ast, precedence)
            }?;

            lhs = Ast::Expression(Expression::Infix(Box::new(lhs), op, Box::new(rhs)))
        }

        Ok(lhs)
    }
    fn parse_integer(&mut self) -> Result<Ast> {
        let Token::Integer(value) = self.tokenizer.next_token() else {
            return Err(anyhow!("Expected integer"));
        };

        Ok(Ast::Constant(Constant::Integer(
            value.parse().map_err(|_| anyhow!("Invalid_string"))?,
        )))
    }

    fn parse_string(&mut self) -> Result<Ast> {
        let Token::String(str) = self.tokenizer.next_token() else {
            return Err(anyhow!("Expected string"));
        };

        Ok(Ast::Constant(Constant::String(
            unescaper::unescape(&str).map_err(|_| anyhow!("Invalid string"))?,
        )))
    }

    fn parse_var_or_func(&mut self, typ: String, is_extern: bool) -> Result<Ast> {
        let Token::Identifier(name) = self.tokenizer.next_token() else {
            return Err(anyhow!("Expected identifier"));
        };

        let peek = self.tokenizer.peek_token();

        if peek == Token::ParenOpen {
            let func_sig = self.parse_function_sig(name, typ, is_extern)?;

            match self.tokenizer.peek_token() {
                Token::Semicolon => {
                    self.tokenizer.next_token();
                    Ok(Ast::FunctionSig(func_sig))
                }
                Token::BraceOpen => {
                    let block = self.parse_block()?;
                    Ok(Ast::Function(Function::new(func_sig, block)))
                }
                _ => Err(anyhow!("Expected '{{' or ';'")),
            }
        } else {
            Ok(Ast::VarDeclaration(VariableDeclaration::new(name, typ)))
        }
    }

    fn parse_function_sig(
        &mut self,
        name: String,
        return_type: String,
        is_extern: bool,
    ) -> Result<FunctionSignature> {
        if self.tokenizer.next_token() != Token::ParenOpen {
            return Err(anyhow!("Expected '('"));
        }

        let mut args = vec![];
        if self.tokenizer.peek_token() == Token::ParenClose {
            self.tokenizer.next_token();
            return Ok(FunctionSignature::new(name, return_type, args, is_extern));
        }

        loop {
            let token = self.tokenizer.next_token();
            let (arg_type, is_const) = match token {
                Token::ConstKeyword => {
                    let Token::Identifier(arg_type) = self.tokenizer.next_token() else {
                        return Err(anyhow!("Expected identifier"));
                    };
                    (arg_type, true)
                }
                Token::Identifier(arg_type) => (arg_type, false),
                Token::VarArgument => {
                    args.push(FunctionArgType::VarArgs);
                    match self.tokenizer.next_token() {
                        Token::ParenClose => break,
                        Token::Comma => {}
                        _ => return Err(anyhow!("Expected ')' or ','")),
                    }
                    continue;
                }
                _ => return Err(anyhow!("Invalid function argument type")),
            };

            let (arg_name, is_pointer) = match self.tokenizer.next_token() {
                Token::Operator(op) => {
                    if op != "*" {
                        return Err(anyhow!("Expected '*'"));
                    };
                    let Token::Identifier(arg_name) = self.tokenizer.next_token() else {
                        return Err(anyhow!("Expected identifier"));
                    };
                    (arg_name, true)
                }
                Token::Identifier(arg_name) => (arg_name, false),
                _ => return Err(anyhow!("Invalid function argument name")),
            };

            args.push(FunctionArgType::Named(FunctionArgument::new(
                arg_name, arg_type, is_const, is_pointer,
            )));

            match self.tokenizer.next_token() {
                Token::ParenClose => break,
                Token::Comma => {}
                _ => return Err(anyhow!("Expected ')' or ','")),
            }
        }

        Ok(FunctionSignature::new(name, return_type, args, is_extern))
    }

    fn parse_block(&mut self) -> Result<Block> {
        if self.tokenizer.next_token() != Token::BraceOpen {
            return Err(anyhow!("Expected '{{'"));
        };

        let mut asts = vec![];

        loop {
            let token = self.tokenizer.peek_token();

            if token == Token::BraceClose {
                self.tokenizer.next_token();
                break;
            } else {
                asts.push(self.parse_statement()?);
            }
        }

        Ok(asts)
    }

    fn parse_statement(&mut self) -> Result<Ast> {
        let token = self.tokenizer.peek_token();
        match token {
            Token::ReturnKeyword => return self.parse_ast(),
            Token::IfKeyword => return self.parse_if_statement(),
            Token::Identifier(_) => {}
            _ => return Err(anyhow!("Expected valid statement")),
        }

        let ast = self.parse_ast()?;

        let peek = self.tokenizer.peek_token();
        if peek == Token::Semicolon {
            self.tokenizer.next_token();
            Ok(ast)
        } else {
            let ast = self.parse_expression(ast, u16::MAX)?;
            if self.tokenizer.next_token() != Token::Semicolon {
                Err(anyhow!("Expected ';'"))
            } else {
                Ok(ast)
            }
        }
    }

    fn parse_call(&mut self, name: String) -> Result<Ast> {
        let token = self.tokenizer.peek_token();
        if token != Token::ParenOpen {
            return Err(anyhow!("Expected '('"));
        }
        self.tokenizer.next_token();

        let mut args = vec![];
        if self.tokenizer.peek_token() == Token::ParenClose {
            return Ok(Ast::Call(FunctionCall::new(name, args)));
        }

        loop {
            let ast = self.parse_ast()?;
            args.push(ast);

            let token1 = self.tokenizer.next_token();
            match token1 {
                Token::ParenClose => break,
                Token::Comma => {}
                _ => return Err(anyhow!("Expected ')' or ','")),
            }
        }

        Ok(Ast::Call(FunctionCall::new(name, args)))
    }

    fn parse_identifier(&mut self, is_extern: bool) -> Result<Ast> {
        let Token::Identifier(ident) = self.tokenizer.next_token() else {
            return Err(anyhow!("Expected identifier"));
        };

        match self.tokenizer.peek_token() {
            Token::Identifier(_) => self.parse_var_or_func(ident, is_extern),
            Token::ParenOpen => self.parse_call(ident),
            Token::Operator(_) => self.parse_expression(Ast::Identifier(ident), u16::MAX),
            _ => Ok(Ast::Identifier(ident)),
        }
    }

    // This also takes care of else statements
    fn parse_if_statement(&mut self) -> Result<Ast> {
        if self.tokenizer.next_token() != Token::IfKeyword {
            return Err(anyhow!("Expected 'if'"));
        }
        if self.tokenizer.next_token() != Token::ParenOpen {
            return Err(anyhow!("Expected '('"));
        }

        let lhs = self.parse_ast()?;
        let expr = self.parse_expression(lhs, u16::MAX)?;
        let Ast::Expression(expr) = expr else {
            return Err(anyhow!("Expected expression"));
        };

        if self.tokenizer.next_token() != Token::ParenClose {
            return Err(anyhow!("Expected ')'"));
        };

        let if_block = self.parse_block()?;

        let else_statement = if self.tokenizer.peek_token() == Token::ElseKeyword {
            self.tokenizer.next_token();
            if self.tokenizer.peek_token() == Token::IfKeyword {
                let Ast::IfStatement(if_statement) = self.parse_if_statement()? else {
                    return Err(anyhow!("Expected if statement"));
                };

                Some(Box::new(ElseStatement::ElseIf(if_statement)))
            } else if self.tokenizer.peek_token() == Token::BraceOpen {
                Some(Box::new(ElseStatement::Else(self.parse_block()?)))
            } else {
                return Err(anyhow!("Expected 'if' or '{{'"));
            }
        } else {
            None
        };

        Ok(Ast::IfStatement(IfStatement::new(
            expr,
            if_block,
            else_statement,
        )))
    }

    fn parse_type(&mut self) -> Result<Ast> {
        let Token::Identifier(ident) = self.tokenizer.next_token() else {
            return Err(anyhow!("Expected identifier"));
        };

        let mut ty = Type::Named(ident);

        while let Token::Operator("*") = self.tokenizer.next_token() {
            ty = Type::Pointer(Box::new(ty))
        }

        Ok(Ast::Type(ty))
    }

    fn expr_parse_ast(&mut self, handled_by_expr: bool) -> Result<Ast> {
        let token = self.tokenizer.peek_token();

        let ast = match token {
            Token::Identifier(_) => self.parse_identifier(false),
            Token::Integer(_) => self.parse_integer(),
            Token::String(_) => self.parse_string(),
            Token::ExternKeyword => {
                self.tokenizer.next_token();
                if !self.tokenizer.peek_token().is_identifier() {
                    return Err(anyhow!("Expected identifier after extern keyword"));
                }

                self.parse_identifier(true)
            }
            Token::ParenOpen => {
                self.tokenizer.next_token();
                let lhs = self.parse_ast()?;
                let expr = self.parse_expression(lhs, u16::MAX)?;
                if self.tokenizer.next_token() != Token::ParenClose {
                    Err(anyhow!("Expected ')'"))
                } else {
                    Ok(expr)
                }
            }
            Token::EOF => Ok(Ast::EOF),
            Token::ReturnKeyword => {
                self.tokenizer.next_token();
                let expr = self.parse_ast()?;
                if self.tokenizer.next_token() != Token::Semicolon {
                    Err(anyhow!("Expected semicolon"))
                } else {
                    Ok(Ast::Return(Box::new(expr)))
                }
            }
            _ => self.parse_statement(),
        }?;

        let peek = self.tokenizer.peek_token();
        if !handled_by_expr {
            if let Token::Operator(_) = peek {
                return self.parse_expression(ast, u16::MAX);
            }
        }

        Ok(ast)
    }

    pub fn parse_ast(&mut self) -> Result<Ast> {
        self.expr_parse_ast(false)
    }
}
