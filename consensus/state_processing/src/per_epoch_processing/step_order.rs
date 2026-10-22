//! Checks that the order of the epoch steps in the Rust code equals the order in the Lean model
//! of Lighthouse's epoch (`process_epoch_lh_order` and `process_epoch_lh_order_fulu` in
//! `proofs/EpochProofs/Sanity/Invariants/LighthouseOrder.lean` and `LighthouseFuluOrder.lean`).
//!
//! The proofs are about the Lean model. A change of the step order on either side makes this
//! test fail, so the model cannot drift from the code without notice.

/// A step of the epoch, with the token that marks it in the Rust and in the Lean source.
struct Step {
    name: &'static str,
    rust: &'static [&'static str],
    lean: &'static [&'static str],
    gloas_only: bool,
}

const STEPS: &[Step] = &[
    Step {
        name: "justification",
        rust: &["process_justification_and_finalization("],
        lean: &["lhJustificationAndFinalization"],
        gloas_only: false,
    },
    Step {
        name: "rows",
        rust: &["single_pass_rows("],
        lean: &["passM"],
        gloas_only: false,
    },
    Step {
        name: "deposit_writes",
        rust: &["apply_deposit_writes("],
        lean: &["lhQueueWrite", "lhNewValidators"],
        gloas_only: false,
    },
    Step {
        name: "pending_consolidations",
        rust: &["process_pending_consolidations("],
        lean: &["process_pending_consolidations", "ebUpdateAt"],
        gloas_only: false,
    },
    Step {
        name: "builder_pending_payments",
        rust: &["process_builder_pending_payments("],
        lean: &["process_builder_pending_payments"],
        gloas_only: true,
    },
    Step {
        name: "proposer_lookahead",
        rust: &["process_proposer_lookahead("],
        lean: &["process_proposer_lookahead"],
        gloas_only: false,
    },
    Step {
        name: "ptc_window",
        rust: &["process_ptc_window("],
        lean: &["process_ptc_window"],
        gloas_only: true,
    },
    Step {
        name: "eth1_data_reset",
        rust: &["process_eth1_data_reset("],
        lean: &["lhEth1DataReset"],
        gloas_only: false,
    },
    Step {
        name: "slashings_reset",
        rust: &["process_slashings_reset("],
        lean: &["lhSlashingsReset"],
        gloas_only: false,
    },
    Step {
        name: "randao_mixes_reset",
        rust: &["process_randao_mixes_reset("],
        lean: &["lhRandaoMixesReset"],
        gloas_only: false,
    },
    Step {
        name: "historical_summaries_update",
        rust: &["process_historical_summaries_update("],
        lean: &["lhHistoricalSummariesUpdate"],
        gloas_only: false,
    },
    Step {
        name: "participation_flag_updates",
        rust: &["process_participation_flag_updates("],
        lean: &["process_participation_flag_updates"],
        gloas_only: false,
    },
    Step {
        name: "sync_committee_updates",
        rust: &["process_sync_committee_updates("],
        lean: &["process_sync_committee_updates"],
        gloas_only: false,
    },
];

const ALTAIR_RS: &str = include_str!("altair.rs");
const SINGLE_PASS_RS: &str = include_str!("single_pass.rs");
const ORDER_LEAN: &str =
    include_str!("../../proofs/EpochProofs/Sanity/Invariants/LighthouseOrder.lean");
const FULU_ORDER_LEAN: &str =
    include_str!("../../proofs/EpochProofs/Sanity/Invariants/LighthouseFuluOrder.lean");

/// The text from `header` to the end of its block: a line `}` for Rust, an empty line for Lean.
fn body<'a>(src: &'a str, header: &str, end: &str) -> &'a str {
    let start = src
        .find(header)
        .unwrap_or_else(|| panic!("`{header}` not found"));
    let rest = &src[start..];
    let len = rest.find(end).unwrap_or(rest.len());
    &rest[..len]
}

/// The steps in `text`, in the order of their first token, with repeats merged.
fn steps_in(text: &str, tokens: impl Fn(&Step) -> &'static [&'static str]) -> Vec<&'static str> {
    let mut found: Vec<(usize, &'static str)> = STEPS
        .iter()
        .flat_map(|step| {
            tokens(step)
                .iter()
                .flat_map(move |token| text.match_indices(token).map(move |(i, _)| (i, step.name)))
        })
        .collect();
    found.sort_by_key(|(i, _)| *i);
    let mut names: Vec<&'static str> = found.into_iter().map(|(_, name)| name).collect();
    names.dedup();
    names
}

fn expected(gloas: bool) -> Vec<&'static str> {
    STEPS
        .iter()
        .filter(|step| gloas || !step.gloas_only)
        .map(|step| step.name)
        .collect()
}

/// The Rust order: `altair::process_epoch` with the body of `process_epoch_single_pass` in the
/// place of its call.
fn rust_order() -> Vec<&'static str> {
    let epoch = body(ALTAIR_RS, "pub fn process_epoch<", "\n}\n");
    let call = epoch
        .find("process_epoch_single_pass(")
        .expect("altair::process_epoch calls process_epoch_single_pass");
    let single_pass = body(SINGLE_PASS_RS, "pub fn process_epoch_single_pass<", "\n}\n");
    let mut order = steps_in(&epoch[..call], |s| s.rust);
    order.extend(steps_in(single_pass, |s| s.rust));
    order.extend(steps_in(&epoch[call..], |s| s.rust));
    order
}

/// The Lean order: justification, then the per-validator pass, then the steps after the pass.
fn lean_order(src: &str, top: &str, tail: &str, mid: &str, rest: &str) -> Vec<&'static str> {
    let mut order = steps_in(body(src, top, "\n\n"), |s| s.lean);
    order.extend(steps_in(body(src, tail, "\n\n"), |s| s.lean));
    order.extend(steps_in(body(src, mid, "\n\n"), |s| s.lean));
    order.extend(steps_in(body(src, rest, "\n\n"), |s| s.lean));
    order
}

#[test]
fn rust_epoch_steps_match_the_gloas_model() {
    assert_eq!(rust_order(), expected(true));
    assert_eq!(
        lean_order(
            ORDER_LEAN,
            "def process_epoch_lh_order ",
            "def lhFullTailWith ",
            "def lhMid ",
            "def lhRestOrder ",
        ),
        expected(true)
    );
}

#[test]
fn rust_epoch_steps_match_the_fulu_model() {
    let fulu: Vec<&str> = rust_order()
        .into_iter()
        .filter(|name| {
            STEPS
                .iter()
                .any(|step| step.name == *name && !step.gloas_only)
        })
        .collect();
    assert_eq!(fulu, expected(false));
    assert_eq!(
        lean_order(
            FULU_ORDER_LEAN,
            "def process_epoch_lh_order_fulu ",
            "def lhFullTailWithFulu ",
            "def lhMidFulu ",
            "def lhRestOrderFulu ",
        ),
        expected(false)
    );
}

#[test]
fn gloas_only_steps_are_gated_on_gloas() {
    let single_pass = body(SINGLE_PASS_RS, "pub fn process_epoch_single_pass<", "\n}\n");
    for step in STEPS.iter().filter(|step| step.gloas_only) {
        for token in step.rust {
            let at = single_pass
                .find(token)
                .unwrap_or_else(|| panic!("{} not called", step.name));
            let open = single_pass[..at].rfind("{\n").expect("guard block");
            let line_start = single_pass[..open].rfind('\n').expect("guard line");
            assert!(
                single_pass[line_start..open].contains("gloas_enabled()"),
                "{} is not gated on Gloas",
                step.name
            );
        }
    }
}
