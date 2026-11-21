# Security policy

Etheorem implements cryptographic primitives (SHA-256) and SSZ
encoding for Ethereum consensus types. Bugs in this code can
have safety-critical consequences for any consumer running it on
mainnet or a beacon-node-adjacent path. We take security reports
seriously.

## Supported versions

The project is pre-alpha and unreleased; only the `master` branch
HEAD is supported. Once we tag releases, this section will list
which release lines receive security fixes.

## Reporting a vulnerability

**Please do not file a public GitHub issue for security bugs.**

Use one of:

1. **GitHub's private vulnerability reporting** (preferred).
   Go to
   <https://github.com/etheorem/etheorem/security/advisories/new>
   and submit a private advisory. This is GitHub's built-in
   responsible-disclosure channel; only the maintainers see the
   report.
2. **Email the maintainers directly** if the GitHub flow is
   unavailable to you. Contact information is in the repository
   `CODEOWNERS` and the maintainers' public GitHub profiles.

Please include:

- A description of the issue and its impact.
- A minimal Lean reproducer (snippet + expected vs actual
  behaviour) or a pointer to the affected file(s) + lines.
- The commit SHA you observed the issue on.
- Your assessment of severity and any constraints on disclosure
  timing.

## What's in scope

In scope:

- **Spec mismatches** in `serialize` / `deserialize` /
  `hashTreeRoot` against the consensus-specs SSZ document or the
  upstream `consensus-spec-tests` vectors.
- **Cache layer correctness**: any input where
  `hashTreeRootCached` diverges from `SSZ.hashTreeRoot` on the
  same view.
- **FFI SHA-256 trust boundary**: input classes where the
  FFI hasher's output disagrees with the pure-Lean `Sha256Spec`
  reference (this would break the axiom
  `sha256Combine_eq_spec` and any proof depending on it).
- **Memory-safety** issues in the FFI C shims
  (`packages/hazmat/*/csrc/`, `packages/LeanPoseidon/csrc/`):
  buffer overflows, use-after-free, etc.
- **Soundness** issues in the verified proofs (`Proofs/`): an
  axiom or `sorry` accepted where it shouldn't be, or a kernel
  bug that lets a false theorem typecheck.

Out of scope:

- Performance regressions (file a normal issue with bench
  numbers).
- Usability issues, documentation gaps, missing features.
- Bugs in the upstream consensus-specs document itself (report
  those to <https://github.com/ethereum/consensus-specs>).
- Bugs in upstream Lean / Lake / mathlib / batteries / OpenSSL
  (report to the respective projects).

## Disclosure timeline

We aim to acknowledge reports within **5 business days** and to
ship a fix within **30 days** for confirmed vulnerabilities,
faster for high-severity issues. We'll coordinate with you on a
disclosure date that allows downstream consumers to update before
public details land.

If you are affiliated with the Ethereum Foundation or any
beacon-client team and want to escalate a finding directly,
please mention so in the report.

## Recognition

Reporters are credited in the relevant release notes unless they
explicitly request anonymity.
