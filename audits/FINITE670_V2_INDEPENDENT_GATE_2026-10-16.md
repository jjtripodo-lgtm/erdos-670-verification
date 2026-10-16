# Finite Erdős 670 v2 independent verification gate (2026-10-16)

## Scope

The current theorem in `jjtripodo-lgtm/erdos-670-fixed-dimension` asserts, for every integer n ≥ 36354, an injective n-point configuration in R^81794, minimum distance ≥ 1, separation ≥ 1 between lengths of distinct unordered non-diagonal edges, and actual diameter < (147/200)n².

The existing Palomar production and Prove2Me preflight evidence in this repository applies **only** to the archived v1 theorem (n ≥ 68000, dimension 458999, diameter < (37/50)n²). It must not be reused as a v2 acceptance claim.

## Existing v2 evidence

The source repository README reports a source-bound 66-module Lean build at trust level zero with an endpoint axiom audit reporting only `propext`, `Classical.choice`, and `Quot.sound`. That is a recorded local build, **not** an independently reproduced clean build. Exact source closure is pinned to commit `f1604c368efce996a9af4d46f581e676e49054f5`.

## Required independent reproduction

1. Check out exactly the pinned v2 commit, not the moving default branch.
2. Confirm all nine external dependency revisions against its lock and verify source/manifest hashes using `python3 verify_release.py` and `python3 verification/finite670/verify_sources.py`.
3. Run `python3 verification/finite670/validate_finite.py` and record output and exit code.
4. In `lean/`, run `lake --no-cache build`, followed by `lake env lean --trust=0 AxiomAudit.lean`; retain logs, toolchain version, hardware/environment, and full exit codes.
5. Check the exact exported theorem declaration `Erdos488.Geometry.SeparatedDistances.FixedDimension.pass5_fixed_dimension_erdos_670` against the manuscript, including unordered edge distinctness and the *actual set* diameter.
6. Report all axioms and any `sorryAx`/nonstandard assumptions. Fail the gate on mismatched statements, extra axioms, incomplete build, or missing logs.
7. Only then propose a version-scoped compatibility port or external platform submission, with separate permission and verification.

## Status

**OPEN / NOT REPRODUCED HERE.** This file records a precise independent verification gate, not a successful test run, mathematical novelty judgment, or external acceptance. No existing pinned Palomar or Prove2Me fixtures should be overwritten.
