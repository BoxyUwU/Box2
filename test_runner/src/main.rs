use std::{path::PathBuf, process::Command};

use ui_test::{default_any_file_filter, OutputConflictHandling};

fn main() {
    Command::new("cargo")
        .args(["build", "-p", "box"])
        .status()
        .unwrap();
    ui_tests("./target/debug/box".into());
}

fn ui_tests(boxl_path: PathBuf) {
    use ui_test::{status_emitter, CommandBuilder, Config, Filter};

    let no_command = CommandBuilder {
        program: "".into(),
        args: vec![],
        out_dir_flag: None,
        input_file_flag: None,
        envs: vec![],
    };

    let should_bless = std::env::args().any(|arg| arg == "--bless");

    let config = Config {
        host: Some("none".into()),
        target: Some("target".into()),
        stderr_filters: Filter::new(),
        stdout_filters: Filter::new(),
        root_dir: format!("./ui_tests").into(),
        mode: ui_test::Mode::Pass,
        program: CommandBuilder {
            program: boxl_path,
            args: vec![],
            out_dir_flag: None,
            input_file_flag: None,
            envs: vec![("NO_COLOR".into(), Some("1".into()))],
        },
        cfgs: no_command.clone(),
        output_conflict_handling: match should_bless {
            false => OutputConflictHandling::Error("--bless".into()),
            true => OutputConflictHandling::Bless,
        },
        dependencies_crate_manifest_path: None,
        dependency_builder: no_command.clone(),
        out_dir: "".into(),
        edition: None,
        skip_files: vec![],
        filter_files: vec![],
        threads: None,
        list: false,
        run_only_ignored: false,
        filter_exact: false,
    };

    ui_test::run_tests_generic(
        vec![config],
        |path, config| {
            path.extension().is_some_and(|ext| ext == "box")
                && default_any_file_filter(path, config)
        },
        |_, _, _| (),
        status_emitter::Text::verbose(),
    )
    .unwrap();
}
