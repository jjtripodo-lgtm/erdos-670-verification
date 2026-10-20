# Fixed-dimension Erdős 670: version-scoped compatibility checks

## Latest paper

The new [Separated distances in fixed dimension](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/blob/fe4e6e004352056dbed6ea5fb051cdb3259ec4b6/paper/2026-10-20/Separated_Distances_in_Fixed_Dimension.pdf)
(20 October 2026) presents the two-circle epsilon family, the dimension-29 prime-first result,
and a separate written all-size R29 corollary. See its
[editable sources and theorem scopes](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/tree/fe4e6e004352056dbed6ea5fb051cdb3259ec4b6/paper/2026-10-20).
The Palomar and Prove2Me checks recorded here remain scoped to the archived
v1.0.0 theorem below; they do not verify this new paper.

The 14 October finite manuscript and proof are in
[erdos-670-fixed-dimension](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension).
For every integer n ≥ 36354, that result gives n points in R^81794 with
separated unordered-edge distances and diameter strictly below (147/200)n².
Its exact [66-module proof source](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/tree/f1604c368efce996a9af4d46f581e676e49054f5/lean)
and [verification scope](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/tree/f1604c368efce996a9af4d46f581e676e49054f5/verification/finite670)
are published separately.

[Result and formalization status, 19 October 2026](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/blob/2caf66c312c5d498d17e1c150588684b66300e68/PUBLIC_STATUS.md)
also explains the exact conjecture-statement adapter, later source-bound replay
evidence reported from a separate provider, and separately scoped internal R29
and epsilon-family formalizations. Those later results do not change the version
checked by the compatibility fixtures in this repository.

## The version checked here

This repository's Palomar and Prove2Me projects concern the archived
**v1.0.0 theorem: n ≥ 68000, dimension 458999, diameter < (37/50)n²**.
They use precisely 54 original source modules from
[commit 1e73a12ff1076dd11affadbf619ddbbef587133e](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/tree/1e73a12ff1076dd11affadbf619ddbbef587133e/lean-fixed670),
archived at [DOI 10.5281/zenodo.23329194](https://doi.org/10.5281/zenodo.23329194).
The statement includes injectivity, unit minimum distance, separation of
distinct unordered non-diagonal edges, and the actual set diameter bound.

These version-specific checks do not verify the revised finite constants.
The code, proof fixtures, dependency pins, and immutable Palomar submission
snapshot remain unchanged.

## Verified results

- Palomar: the 54-module Lean 4.35.0-rc2 build, final axiom audit and intact
  sandboxed Comparator passed in
  [run 38337326194](https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/38337326194).
  Immutable snapshot `5510ffd94156d48dbe393ac619586b935212da79` subsequently
  passed the [complete official preflight](https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/38340299337)
  and [production verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/38342636995).
  The default Lean kernel, con-ron and NanoDa accepted that version
- Prove2Me extraction: the source-derived declaration/type/position extraction
  passed in [run 38350587663](https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/38350587663)
- Prove2Me transformed-node preflight: [run 38424315562](https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/38424315562)
  passed at harness commit `15b2e692621da7b01ea2412a89529860d78c8f09`.
  It compiled all 48 targets and passed the 20 theorem/solution type-and-axiom
  checks plus 92 definition axiom reports. This is a preflight result;
  no Prove2Me submission or acceptance is asserted

The permitted proof axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Deliberate statement stubs are not proof certificates.
Mechanical checks do not establish editorial acceptance, specialist
mathematical review, priority, or journal acceptance.

## Reproduce and inspect

- [Palomar preparation-state README, 13 October 2026](https://github.com/jjtripodo-lgtm/erdos-670-verification/blob/5510ffd94156d48dbe393ac619586b935212da79/palomar/README.md):
  the immutable submission package retains its earlier preparation-time status
  and scoped migration repairs. The later mechanical outcomes are reported above
- [Prove2Me extraction](extraction/README.md) and [adapter](extraction/adapter/README.md):
  frozen inputs, export allowlist, execution and resource gates
- [Transformed-node checks](nodes/README.md): exact source fixtures, statement
  comparisons, synchronous kernel-backed solution checks and negative controls
- [Original-source and migration hashes](SOURCE_MANIFEST.json);
  [recorded compatibility repairs](PALOMAR_MIGRATION_PATCHES.json)

Offline checks from this repository:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 extraction/check_payload.py
PYTHONDONTWRITEBYTECODE=1 python3 scripts/test_adapter.py
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s nodes -p 'test_*.py'
```

Palomar uses Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`;
Prove2Me uses Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. Never replace these
version-specific pins with the current finite source without a separate port
and complete validation.

Existing compatibility jobs use standard public runners, read-only repository
permissions, no secrets, no artifact uploads and no reusable GitHub-cache
writes. The separate manual extraction and full Palomar workflows retain their
documented storage, sandbox, and explicit-execution gates. A passing check does
not authorize another platform submission.

## Rights

This code-only harness and the formalization are MIT licensed. The manuscript
is linked, not copied or relicensed here; each manuscript version carries its
own rights in the source repository. Upstream dependencies retain their licenses.

