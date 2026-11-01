#![cfg(unix)]

//! Test driver boundaries without compiling the workspace recursively.
use std::fs;
use std::os::unix::fs::{FileTypeExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

struct Scratch(PathBuf);
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn driver_guards_checkout_identity_and_keeps_the_full_gate_unfiltered() {
    tauto_messages::install();
    let root = std::env::temp_dir().join(format!(
        "tauto-driver-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    fs::create_dir(&root).unwrap();
    let scratch = Scratch(root.canonicalize().unwrap());
    let root = &scratch.0;
    let bin = root.join("bin");
    fs::create_dir(&bin).unwrap();
    let cargo = bin.join("cargo");
    fs::write(&cargo, "#!/bin/bash\nprintf '%s|%s|%s\\n' \"$*\" \"$CARGO_TARGET_DIR\" \"$CARGO_BUILD_BUILD_DIR\" >> \"$TEST_LOG\"\nif [[ $1 == --config ]]; then shift 2; fi\nif [[ ${FAIL_TEST:-} == 1 && $1 == test ]]; then exit 17; fi\n").unwrap();
    fs::set_permissions(&cargo, fs::Permissions::from_mode(0o755)).unwrap();
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/test.sh");
    let repos = [root.join("one space 日本語"), root.join("two space café")];
    for repo in &repos {
        fs::create_dir_all(repo.join("scripts")).unwrap();
        fs::copy(&script, repo.join("scripts/test.sh")).unwrap();
    }
    let repos = repos.map(|repo| repo.canonicalize().unwrap());
    let log = root.join("commands");
    let mut paths = vec![bin];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let path = std::env::join_paths(paths).unwrap();
    let run = |repo: &Path, args: &[&str], overrides: &[(&str, &Path)]| -> Output {
        let mut command = Command::new("bash");
        command
            .arg(repo.join("scripts/test.sh"))
            .args(args)
            .env("PATH", &path)
            .env("TEST_LOG", &log)
            .env_remove("CARGO_TARGET_DIR")
            .env_remove("CARGO_BUILD_BUILD_DIR")
            .env_remove("TAUTO_TEST_CACHE_ROOT")
            .env_remove("FAIL_TEST");
        for (name, value) in overrides {
            command.env(name, value);
        }
        let mut child = command
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(10);
        while child.try_wait().unwrap().is_none() {
            if Instant::now() >= deadline {
                let _ = child.kill();
                let _ = child.wait();
                panic!("test driver did not terminate: {args:?}");
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        child.wait_with_output().unwrap()
    };
    let count = || fs::read_to_string(&log).unwrap_or_default().lines().count();
    let reject = |output: Output| {
        assert_eq!(
            output.status.code(),
            Some(2),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    };
    reject(run(&repos[0], &["full", "--skip", "x"], &[]));
    reject(run(&repos[0], &["focused"], &[]));
    for argument in [
        "--target-dir=x",
        "--manifest-path=x",
        "--config=x",
        "-Cx",
        "-m",
        "-mx",
        "-qm",
        "-vm",
        "-qC",
        "-pvalue",
    ] {
        reject(run(&repos[0], &["focused", argument], &[]));
    }
    assert_eq!(count(), 0);
    assert!(
        run(
            &repos[0],
            &["focused", "-p", "tauto-build", "--test", "build_rs"],
            &[]
        )
        .status
        .success()
    );
    assert!(run(&repos[0], &["full"], &[]).status.success());
    let commands = fs::read_to_string(&log).unwrap();
    let lines: Vec<_> = commands.lines().collect();
    assert_eq!(lines.len(), 4);
    assert!(lines[0].contains(" test --locked -p tauto-build --test build_rs|"));
    assert!(lines[1].contains(" test --locked --workspace|"));
    assert!(lines[2].contains("check meta/KernelSafe.taut"));
    assert!(lines[3].contains("fmt --check"));
    assert_eq!(
        run(&repos[0], &["full"], &[("FAIL_TEST", Path::new("1"))])
            .status
            .code(),
        Some(17)
    );
    assert_eq!(count(), 5, "a failed workspace gate stops later commands");
    let target = repos[0].join("target");
    reject(run(&repos[1], &["full"], &[("CARGO_TARGET_DIR", &target)]));
    let unowned = root.join("unowned");
    fs::create_dir(&unowned).unwrap();
    fs::write(unowned.join("keep"), "preserve").unwrap();
    reject(run(&repos[0], &["full"], &[("CARGO_TARGET_DIR", &unowned)]));
    assert_eq!(
        fs::read_to_string(unowned.join("keep")).unwrap(),
        "preserve"
    );
    assert_eq!(count(), 5);
    let regular = root.join("not-a-directory");
    fs::write(&regular, "keep").unwrap();
    reject(run(&repos[0], &["full"], &[("CARGO_TARGET_DIR", &regular)]));
    assert_eq!(fs::read_to_string(&regular).unwrap(), "keep");
    let linked = root.join("linked-marker");
    fs::create_dir(&linked).unwrap();
    std::os::unix::fs::symlink(&regular, linked.join(".tauto-checkout")).unwrap();
    reject(run(&repos[0], &["full"], &[("CARGO_TARGET_DIR", &linked)]));
    let fifo = root.join("fifo-marker");
    fs::create_dir(&fifo).unwrap();
    assert!(
        Command::new("mkfifo")
            .arg(fifo.join(".tauto-checkout"))
            .status()
            .unwrap()
            .success()
    );
    reject(run(&repos[0], &["full"], &[("CARGO_TARGET_DIR", &fifo)]));
    assert!(
        fs::symlink_metadata(fifo.join(".tauto-checkout"))
            .unwrap()
            .file_type()
            .is_fifo()
    );
    assert_eq!(count(), 5);
    let exact = root.join("exact");
    let build = root.join("build output \"日本語\"");
    let overrides = [
        ("CARGO_TARGET_DIR", exact.as_path()),
        ("CARGO_BUILD_BUILD_DIR", build.as_path()),
    ];
    assert!(
        run(&repos[0], &["focused", "-p", "tauto-build"], &overrides)
            .status
            .success()
    );
    let last = fs::read_to_string(&log)
        .unwrap()
        .lines()
        .last()
        .unwrap()
        .to_owned();
    assert!(
        last.ends_with(&format!("|{}|", exact.display())),
        "the fixed build-dir environment must not leak to child Cargo: {last}"
    );
    assert!(
        last.contains(&format!("build.build-dir={:?}", build.to_str().unwrap())),
        "the exact outer build directory is passed as one configuration value: {last}"
    );
    reject(run(
        &repos[1],
        &["full"],
        &[("CARGO_BUILD_BUILD_DIR", &build)],
    ));
    let shared = root.join("shared");
    for repo in &repos {
        assert!(
            run(repo, &["full"], &[("TAUTO_TEST_CACHE_ROOT", &shared)])
                .status
                .success()
        );
        let namespace = shared
            .join("checkouts")
            .join(repo.strip_prefix("/").unwrap());
        assert_eq!(
            fs::read_to_string(namespace.join(".tauto-checkout")).unwrap(),
            repo.to_str().unwrap()
        );
    }
    let before = count();
    reject(run(
        &repos[0],
        &["full"],
        &[
            ("TAUTO_TEST_CACHE_ROOT", &shared),
            ("CARGO_TARGET_DIR", &exact),
        ],
    ));
    let template = root.join("{workspace-path-hash}");
    reject(run(
        &repos[0],
        &["full"],
        &[("CARGO_BUILD_BUILD_DIR", &template)],
    ));
    assert_eq!(count(), before);
    assert!(
        run(
            &repos[0],
            &["focused", "-vv", "-p", "tauto-build", "--", "-qm"],
            &[]
        )
        .status
        .success()
    );
}
