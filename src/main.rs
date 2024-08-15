use clap::Parser;

#[derive(Parser)]
struct Args {
    from_file: std::path::PathBuf,
    to_file: std::path::PathBuf,

    /// Context lines to include before and after the matching line
    #[clap(short, long, default_value = "3")]
    context: usize,
}

fn main() {
    let args = Args::parse();

    let from_meta = std::fs::metadata(&args.from_file).expect("from_file not found");
    let to_meta = std::fs::metadata(&args.to_file).expect("to_file not found");

    let from_file = std::fs::read_to_string(&args.from_file).expect("from_file not found");
    let to_file = std::fs::read_to_string(&args.to_file).expect("to_file not found");

    let from_lines = from_file.split_inclusive('\n').collect::<Vec<_>>();
    let to_lines = to_file.split_inclusive('\n').collect::<Vec<_>>();

    let outlines = patiencediff::unified_diff(
        &from_lines,
        &to_lines,
        Some(args.from_file.to_string_lossy().as_ref()),
        Some(args.to_file.to_string_lossy().as_ref()),
        None,
        None,
        Some(args.context),
    );

    for line in &outlines {
        print!("{}", line);
    }

    if outlines.is_empty() {
        std::process::exit(0);
    } else {
        std::process::exit(1);
    }
}
