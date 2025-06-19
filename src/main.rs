use crate::ast::{Ast, Parser};
use crate::backend::IrBuilder;
use crate::tokenizer::Tokenizer;
use clap::error::ErrorKind;
use clap::{CommandFactory, Parser as ClapParser};
use clio::{ClioPath, Input};
use inkwell::context::Context;
use std::io::Read;
use std::path::Path;

pub mod ast;
pub mod backend;
pub mod tokenizer;
pub mod utils;

#[derive(Debug, clap::Parser)]
#[command(
    version = "0.0.1",
    about = "A barebones c compiler made with Rust and LLVM"
)]
struct Args {
    /// The file that will get compiled into machine code
    #[clap(value_name = "file", value_parser = clap::value_parser!(Input).exists().is_file())]
    file: Input,

    /// Where the object file should be outputted to
    #[clap(short, long, value_name = "output", value_parser = clap::value_parser!(ClioPath).is_file())]
    output: Option<ClioPath>,

    /// If provided, the compiler will output human-readable LLVM IR to the specified directory
    #[clap(long = "output-ir", value_name = "output", value_parser = clap::value_parser!(ClioPath).is_file())]
    ir_output: Option<ClioPath>,
}

fn main() -> anyhow::Result<()> {
    let mut args = Args::parse();
    if args.output.is_none() && args.ir_output.is_none() {
        Args::command()
            .error(
                ErrorKind::MissingRequiredArgument,
                "Either `output` or `ir-output` needs to be specified",
            )
            .exit();
    }

    let mut file_content = String::new();
    args.file.read_to_string(&mut file_content)?;

    let path_string = args.file.path().to_string();
    let path = Path::new(&path_string);
    let Some(module_name) = path.file_name() else {
        println!("Input file is invalid");
        return Ok(());
    };
    let module_name = module_name.to_str().expect("Module name").to_string();

    let mut parser = Parser::new(Tokenizer::new(&file_content));
    let context = Context::create();
    let mut builder = IrBuilder::new(&context, &module_name);

    loop {
        let ast = parser.parse_ast()?;

        if ast == Ast::EOF {
            break;
        }

        builder.visit_ast(ast)?;
    }

    if let Some(output) = args.output {
        builder.output_object(&output)?;
    }
    if let Some(ir_output) = args.ir_output {
        builder.output_ir(&ir_output)?;
    }

    Ok(())
}
