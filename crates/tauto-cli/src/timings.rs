//! Sequential wall-clock build phases, reported with `--timings`. No source or environment values
//! are stored in the report. The clock is read only while reporting is enabled.

use std::io::Write;
use std::time::{Duration, Instant};

use serde::Serialize;

use crate::i18n;
use tauto_rustgen::WriteStats;

#[derive(Clone, Copy)]
pub(crate) enum Format {
    Text,
    Json,
}

#[derive(Serialize)]
struct Phase {
    name: &'static str,
    duration_ns: u64,
    status: &'static str,
}

#[derive(Serialize)]
struct GeneratedSources {
    provenance: &'static str,
    hits: usize,
    misses: usize,
}

#[derive(Serialize)]
struct Cache {
    generated_sources: Option<GeneratedSources>,
    native: &'static str,
    proof: &'static str,
}

#[derive(Serialize)]
struct Report {
    schema_version: u32,
    kind: &'static str,
    backend: &'static str,
    target: &'static str,
    status: &'static str,
    duration_ns: u64,
    phases: Vec<Phase>,
    cache: Cache,
    #[serde(skip)]
    current: Option<(&'static str, Duration)>,
}

fn nanos(duration: Duration) -> u64 {
    duration.as_nanos().try_into().unwrap_or(u64::MAX)
}

impl Report {
    fn new(backend: &'static str, target: &'static str) -> Self {
        Self {
            schema_version: 1,
            kind: "tauto.build.timings",
            backend,
            target,
            status: "failed",
            duration_ns: 0,
            phases: Vec::new(),
            cache: Cache {
                generated_sources: None,
                native: "not_run",
                proof: "not_run",
            },
            current: Some(("input", Duration::ZERO)),
        }
    }

    fn end_phase(&mut self, elapsed: Duration, status: &'static str) {
        if let Some((name, start)) = self.current.take() {
            self.phases.push(Phase {
                name,
                duration_ns: nanos(elapsed.saturating_sub(start)),
                status,
            });
        }
    }

    fn phase_at(&mut self, name: &'static str, elapsed: Duration) {
        self.end_phase(elapsed, "ok");
        self.current = Some((name, elapsed));
        if name == "tote_load_check_extract" {
            self.cache.proof = "unknown";
        }
        if name == "native_compile" {
            self.cache.native = "unknown";
        }
    }

    fn finish_at(&mut self, success: bool, elapsed: Duration) {
        self.status = if success { "ok" } else { "failed" };
        self.end_phase(elapsed, self.status);
        self.duration_ns = nanos(elapsed);
    }

    fn write(&self, format: Format, out: &mut impl Write) -> std::io::Result<()> {
        match format {
            Format::Json => {
                serde_json::to_writer(&mut *out, self)?;
                writeln!(out)
            }
            Format::Text => {
                writeln!(
                    out,
                    "{}",
                    i18n::t!(
                        "timings-heading",
                        status = self.status,
                        backend = self.backend,
                        target = self.target
                    )
                )?;
                for phase in &self.phases {
                    writeln!(
                        out,
                        "  {:<24} {:>12.3} ms  {}",
                        phase.name,
                        phase.duration_ns as f64 / 1_000_000.0,
                        phase.status
                    )?;
                }
                writeln!(
                    out,
                    "  {:<24} {:>12.3} ms",
                    i18n::t!("timings-total"),
                    self.duration_ns as f64 / 1_000_000.0
                )?;
                if let Some(files) = &self.cache.generated_sources {
                    writeln!(
                        out,
                        "  {}",
                        i18n::t!(
                            "timings-generated-sources",
                            unchanged = files.hits,
                            written = files.misses
                        )
                    )?;
                } else {
                    writeln!(out, "  {}", i18n::t!("timings-generated-unknown"))?;
                }
                writeln!(
                    out,
                    "  {}",
                    i18n::t!("timings-native-cache", cache = self.cache.native)
                )?;
                writeln!(
                    out,
                    "  {}",
                    i18n::t!("timings-proof-cache", cache = self.cache.proof)
                )
            }
        }
    }
}

pub(crate) struct Timings {
    active: Option<(Format, Instant, Report)>,
}

impl Timings {
    pub(crate) fn new(format: Option<Format>, backend: &str, target: &str) -> Self {
        Self {
            active: format.map(|format| {
                let (backend, target) = match (backend, target) {
                    ("rust", "wasm32-wasip1") => ("rust", "wasm32-wasip1"),
                    ("rust", "wasm32-unknown-unknown") => ("rust", "wasm32-unknown-unknown"),
                    ("rust", _) => ("rust", "host"),
                    ("javascript", "node") => ("javascript", "node"),
                    ("javascript", "browser") => ("javascript", "browser"),
                    _ => unreachable!("build options are validated before timing starts"),
                };
                (format, Instant::now(), Report::new(backend, target))
            }),
        }
    }

    pub(crate) fn phase(&mut self, name: &'static str) {
        if let Some((_, start, report)) = &mut self.active {
            report.phase_at(name, start.elapsed());
        }
    }

    pub(crate) fn written(&mut self, stats: WriteStats) {
        if let Some((_, _, report)) = &mut self.active {
            let sources = report
                .cache
                .generated_sources
                .get_or_insert(GeneratedSources {
                    provenance: "content_equality",
                    hits: 0,
                    misses: 0,
                });
            sources.hits += stats.unchanged;
            sources.misses += stats.written;
        }
    }

    pub(crate) fn finish(mut self, success: bool) {
        if let Some((format, start, report)) = &mut self.active {
            report.finish_at(success, start.elapsed());
            // Reporting cannot change the build's status, including when stderr
            // is closed. Ordinary diagnostics are emitted before this report.
            let _ = report.write(*format, &mut std::io::stderr().lock());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_boundaries_include_total_without_overlap() {
        let mut report = Report::new("rust", "host");
        report.phase_at("parse_expand", Duration::from_nanos(10));
        report.phase_at("check", Duration::from_nanos(25));
        report.finish_at(false, Duration::from_nanos(40));
        let mut json = Vec::new();
        report.write(Format::Json, &mut json).unwrap();
        let value: serde_json::Value = serde_json::from_slice(&json).unwrap();
        assert_eq!(value["schema_version"], 1);
        assert_eq!(value["kind"], "tauto.build.timings");
        assert_eq!(value["duration_ns"], 40);
        assert_eq!(value["status"], "failed");
        assert_eq!(value["phases"][0]["duration_ns"], 10);
        assert_eq!(value["phases"][1]["duration_ns"], 15);
        assert_eq!(value["phases"][1]["status"], "ok");
        assert_eq!(value["phases"][2]["duration_ns"], 15);
        assert_eq!(value["phases"][2]["status"], "failed");
        assert_eq!(value["cache"]["native"], "not_run");
        assert!(value["cache"]["generated_sources"].is_null());
        assert!(value.get("current").is_none());
    }

    #[test]
    fn repeated_phases_are_sequential_and_native_reuse_is_unknown() {
        let mut report = Report::new("javascript", "browser");
        report.phase_at("codegen_write", Duration::from_nanos(1));
        report.phase_at("native_compile", Duration::from_nanos(2));
        report.phase_at("codegen_write", Duration::from_nanos(5));
        report.finish_at(true, Duration::from_nanos(8));
        assert_eq!(report.phases.iter().map(|p| p.duration_ns).sum::<u64>(), 8);
        assert_eq!(report.cache.native, "unknown");
        assert_eq!(report.status, "ok");
        let mut text = Vec::new();
        report.write(Format::Text, &mut text).unwrap();
        assert!(
            String::from_utf8(text)
                .unwrap()
                .contains("native cache: unknown")
        );
    }

    #[test]
    fn disabled_reporting_has_no_clock_or_records() {
        let mut timings = Timings::new(None, "rust", "host");
        timings.phase("check");
        timings.written(WriteStats {
            unchanged: 1,
            written: 2,
        });
        assert!(timings.active.is_none());
    }
}
