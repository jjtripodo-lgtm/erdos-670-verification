# Fixed-dimension Erdős 670 compatibility checks

This repository is a small mechanical test harness for the public formalization
of fixed-dimensional separated Euclidean distances. It is not a Palomar
submission repository or a Prove2Me node package.

The paper and original formalization remain in the separate
[frozen v1.0.0 release](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/releases/tag/v1.0.0).
Every run reads precisely 54 Lean source files from
[commit 1e73a12ff1076dd11affadbf619ddbbef587133e](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/tree/1e73a12ff1076dd11affadbf619ddbbef587133e/lean-fixed670).
It neither changes that repository nor copies the paper into this one.

## The theorem's scope

For every natural number n at least 68000, the theorem constructs n injectively
indexed points in the single fixed Euclidean space R^458999. Distances between
distinct points are at least one; distances attached to different unordered
non-diagonal pairs differ by at least one; and every pair distance and the
diameter are strictly below (37/50)n². These are explicit sufficient bounds,
not claims of optimal dimension, threshold, coefficient, or priority.

## Two separate checks

- Palomar compatibility: Lean 4.35.0-rc2, Mathlib
  065356127b1dc0016f66b7283ce0ce2c4055aa55. The deterministic adapter adds module
  syntax and public imports/sections, then applies exactly three recorded
  compatibility edits. It builds all 54 modules and Solution, checks the final
  theorem's axioms, and runs the intact official `lake comparator` sandbox.
- Prove2Me compatibility: Lean 4.33.1, Mathlib
  0df444a360eaa60ab8c11dca51a86af692955474. The 54 source files are unchanged,
  `autoImplicit = false` is enabled, and the job builds every source module
  and checks the final theorem's axioms. It does not import or upload a node.

The permitted axioms are propext, Quot.sound, and Classical.choice. The Palomar
Challenge template contains one deliberate proof hole defining the statement
Comparator must match. Challenge alone is not a proof; Solution imports the
substantive development and never imports Challenge.

See the individual workflow step outcomes and logs for actual results. A pass
establishes only the checks that ran. It does not establish full Palomar
verification with independent kernels, either platform's acceptance,
independent mathematical review, priority, or journal acceptance.

## Reproducibility and runtime boundaries

SOURCE_MANIFEST.json contains every original and candidate source SHA256.
PALOMAR_MIGRATION_PATCHES.json records the three exact edits and reasons.
FIXTURE_SHA256.json covers the minimal source/configuration templates; Lean
templates end in `.lean.txt` so this harness has no repository-level Lean
project. Generated candidate trees contain only the 54 proof files and the
platform's allowlisted Lean/configuration/license files. Submission metadata,
importers, manuscript files, reports, and prebuilt proof objects are omitted.

Each matrix job gets a separate standard ubuntu-22.04 full virtual machine in
a public repository. There are no third-party Actions, repository secrets,
private fetches, OAuth tools, paid runners, platform API calls, artifact
uploads, or reusable GitHub cache writes. Only ordinary job logs and summaries
are retained, according to the repository's GitHub retention settings.

The harness and dependency commits are exact Git hashes. Official Lean
archives and bubblewrap 0.12.0 are SHA256-checked. Ubuntu build prerequisites
come from signed apt repositories, with installed versions logged; the hosted
OS image and those package versions are not claimed to be immutable. Mathlib's
pinned cache client reads the targeted canonical master/legacy cache using its
source-derived cache keys. These build-cache objects are not an additional
per-file SHA256 lock, and no fork cache or custom cache endpoint is used.

The bubblewrap release and build flags follow
[the pinned official Palomar installer](https://github.com/PalomarRegistry/PalomarSubmission/blob/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44/scripts/install_bwrap.sh).
The harness does not change AppArmor profiles, sysctl settings, or the
Comparator sandbox. A full namespace/mount smoke test runs before downloading
Lean. Namespace or mount restrictions are reported as host blockers.

The runner must begin with at least 11 GiB free; at least 6 GiB is required
before reading Mathlib's cache and 3 GiB before Comparator. Each guarded
command stops if free disk falls below 2 GiB. These are capacity checks, not a
guarantee that a future runner image will fit. No unrelated runner files are
deleted to make room. Jobs have a 180-minute limit.

## Offline adapter check

With a local checkout of the frozen source, run:

```sh
python3 scripts/test_adapter.py --source-root /path/to/checkout/lean-fixed670
python3 scripts/make_candidate.py palomar --source-root /path/to/checkout/lean-fixed670 --output /tmp/palomar-candidate
python3 scripts/check_candidate.py palomar /tmp/palomar-candidate
```

Without `--source-root`, make_candidate.py reads only the pinned 54 public
source files and rejects any hash mismatch before creating its output tree.
The GitHub workflow runs on relevant pushes to main or manual dispatch. Initial
publication and subsequent pushes must be explicitly authorized by the owner.

## License

This harness, its code templates, and the original formalization are MIT
licensed. The manuscript in the source repository has separate reserved-rights
terms and is referenced only by link; it is not included or relicensed here.
