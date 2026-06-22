## Summary

<!-- 1–3 sentences. What does this PR change and why?
     Link the issue(s) it addresses if applicable. -->

## What changed

<!-- Bulleted list of the concrete code / doc changes. Group by
     subpackage if the PR spans multiple. -->

- 
- 

## Test plan

<!-- How did you verify the change? Check what applies. -->

- [ ] `lake build` (full monorepo, on the pinned toolchain) is green.
- [ ] Per-package test suites pass:
  - [ ] `lake build LeanSha256Tests`
  - [ ] `lake build SizzLeanTests`
  - [ ] `just test-ethcl`
- [ ] If this touches spec types or cache behaviour:
      `just ethcl-conformance` is green.
- [ ] If this touches a bench-measured hot path: included
      before/after `lake exe ssz_bench` TSV (or relevant rows) in
      the PR description.
- [ ] New SSZ shapes / cache cases come with a `native_decide` or
      property test that exercises them.

## Risk / trust footprint

<!-- Does this PR add or remove any axiom, `sorry`, `partial def`,
     `native_decide` invocation, `unsafe` block, or `@[extern]`
     declaration? List them. If none, write "none". -->

## Notes for reviewers

<!-- Anything that helps the reviewer get oriented: design
     trade-offs considered, decisions made under ambiguity,
     follow-ups deferred. -->
