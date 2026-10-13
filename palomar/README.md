# Fixed-dimensional separated Euclidean distances

This code-only candidate ports the formalization from the [frozen v1.0.0 release](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/releases/tag/v1.0.0), archived as [DOI 10.5281/zenodo.23329194](https://doi.org/10.5281/zenodo.23329194), source commit `1e73a12ff1076dd11affadbf619ddbbef587133e`, to Lean 4.35.0-rc2 and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

For every natural number `n >= 68000`, the theorem constructs `n` injectively indexed points in the single fixed Euclidean space `R^458999`. Distances between distinct points are at least one; distances belonging to distinct unordered non-diagonal pairs differ by at least one; and every pair distance and the diameter are strictly below `(37/50)n^2`. These are sufficient bounds, not optimality or priority claims.

The exact declaration is `Erdos488.Geometry.SeparatedDistances.FixedDimension.fixed_dimension_erdos_670`. Start with `Challenge.lean` for the standalone statement and definitions, then `Solution.lean` for the substantive proof import. Challenge's deliberate proof placeholder is not itself a proof. Solution never imports Challenge.

## Reproduce

The complete dependency lock is in `lake-manifest.json`. With the exact toolchain installed:

```sh
lake build
lake env lean --trust=0 AxiomAudit.lean
lake comparator --config comparator.json
```

Comparator requires Linux and an operational bubblewrap sandbox. Never disable the sandbox. The project libraries compile with `--trust=0`; the only permitted final-theorem axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The local and hosted full proof builds and final axiom audits passed. The [hosted sandboxed Comparator run](https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/38337326194/job/115100254416) also passed on 2026-10-13: the standard Lean kernel accepted the exported solution and Comparator accepted the statement/definition match. No Palomar submission, independent-kernel verdict, editorial acceptance, independent mathematical review, or priority determination is claimed.

`SOURCE_MANIFEST.json` records every original and ported proof-source hash. `MIGRATION_PATCHES.json` records the three narrow compatibility repairs beyond the module/public-visibility migration. The statement and mathematical definitions are unchanged.

## License and manuscript

Software is covered by the original MIT license, reproduced in the repository-root [`LICENSE`](../LICENSE). The manuscript stays in the source repository under its separate reserved-rights terms. It is linked and cited, not copied or relicensed here. Third-party dependencies retain their own licenses. `formalization.yaml` records provenance and AI assistance separately from human responsibility.
