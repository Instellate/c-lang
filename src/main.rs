use crate::ast::{Ast, Parser};
use crate::backend::IrBuilder;
use crate::tokenizer::Tokenizer;
use inkwell::context::Context;

pub mod ast;
pub mod backend;
pub mod tokenizer;

const STR: &str = include_str!("c-lang.c");

fn main() -> anyhow::Result<()> {
    let mut parser = Parser::new(Tokenizer::new(&STR));

    let context = Context::create();
    let mut builder = IrBuilder::new(&context);

    loop {
        let ast = parser.parse_ast()?;

        if ast == Ast::EOF {
            break;
        }

        builder.visit_ast(ast)?;
    }

    println!("{}", builder);
    builder.output_object()?;

    Ok(())
}
