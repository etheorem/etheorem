//! The libssz side of the SizzLean comparative benchmark.
//!
//! ```text
//! libssz-compbench <state.ssz> <reps>
//! ```
//!
//! The harness decodes the `BeaconState` the Lean side emitted, roots it,
//! applies the scenario's writes, and roots it again, timing each of the five
//! phases. It reports a zero `wrap_ns`: libssz roots the decoded value
//! directly, with no wrapping step of its own. It prints one JSON object per line on stdout, with the same keys
//! the Lean and the Python harnesses print, so the driver reads all three the
//! same way. Diagnostics go to stderr.
//!
//! libssz keeps no Merkle cache. Its `hash_tree_root` is a pure function of
//! the whole value, so the second root costs what the first one did. That is
//! the library's design, and the report says so rather than reading the
//! number as a shortfall.

mod types;

use std::hint::black_box;
use std::time::Instant;

use libssz::SszDecode;
use libssz_merkle::{HashTreeRoot, Sha2Hasher};
use types::BeaconState;

/// Writes per shape in the `update1000` scenario. Four shapes, so the
/// scenario writes 1000 fields.
const WRITES_PER_SHAPE: usize = 250;

/// One byte of a 32-byte root, from a seed. The Lean copy is
/// `SizzLeanBench.CompBench.Fixture.byte32`; the two must agree, because the
/// roots the writes produce are compared across the harnesses.
fn byte32(seed: usize, pos: usize) -> u8 {
    ((seed * 31 + pos * 7 + 11) % 256) as u8
}

/// A 32-byte root from a seed.
fn mk_root(seed: usize) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (pos, byte) in out.iter_mut().enumerate() {
        *byte = byte32(seed, pos);
    }
    out
}

/// The single write: bump `slot` by one.
fn write_one(state: &mut BeaconState) {
    state.slot += 1;
}

/// The thousand writes, in the order the Lean harness applies them:
/// validators, balances, `block_roots`, `randao_mixes`.
fn write_thousand(state: &mut BeaconState) {
    for i in 0..WRITES_PER_SHAPE {
        state.validators[i].effective_balance += 1_000_000;
    }
    for i in 0..WRITES_PER_SHAPE {
        state.balances[i] += 12_345;
    }
    for i in 0..WRITES_PER_SHAPE {
        state.block_roots[i] = mk_root(i + 90_000);
    }
    for i in 0..WRITES_PER_SHAPE {
        state.randao_mixes[i] = mk_root(i + 95_000);
    }
}

/// A root as the lowercase `0x` hex string every harness prints.
fn root_hex(root: &[u8; 32]) -> String {
    let mut out = String::with_capacity(66);
    out.push_str("0x");
    for byte in root {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}

/// Run one repetition of one scenario and print its line.
fn run_once(bytes: &[u8], scenario: &str, rep: usize, write: fn(&mut BeaconState)) {
    let hasher = Sha2Hasher;

    let t0 = Instant::now();
    let mut state = BeaconState::from_ssz_bytes(bytes).expect("fixture did not decode");
    black_box(&state);
    let t1 = Instant::now();

    let root1 = state.hash_tree_root(&hasher);
    black_box(&root1);
    let t2 = Instant::now();

    write(&mut state);
    black_box(&state);
    let t3 = Instant::now();

    let root2 = state.hash_tree_root(&hasher);
    black_box(&root2);
    let t4 = Instant::now();

    // `wrap_ns` is zero because libssz has no wrapping step: it roots the
    // decoded value directly. The key is printed anyway so every harness
    // emits the same line shape.
    println!(
        "{{\"impl\": \"libssz\", \"scenario\": \"{}\", \"rep\": {}, \
         \"deser_ns\": {}, \"wrap_ns\": 0, \"root1_ns\": {}, \"update_ns\": {}, \
         \"root2_ns\": {}, \"root1\": \"{}\", \"root2\": \"{}\"}}",
        scenario,
        rep,
        (t1 - t0).as_nanos(),
        (t2 - t1).as_nanos(),
        (t3 - t2).as_nanos(),
        (t4 - t3).as_nanos(),
        root_hex(&root1),
        root_hex(&root2),
    );
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: libssz-compbench <state.ssz> <reps>");
        std::process::exit(1);
    }
    let bytes = std::fs::read(&args[1]).expect("cannot read the fixture");
    let reps: usize = args[2].parse().expect("repetition count is not a number");
    eprintln!("fixture bytes: {}", bytes.len());

    for rep in 0..reps {
        run_once(&bytes, "update1", rep, write_one);
    }
    for rep in 0..reps {
        run_once(&bytes, "update1000", rep, write_thousand);
    }
}
