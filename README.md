# Fixed-dimension Erdős 670 compatibility checks

This repository contains the code-only [Palomar proof project](palomar/README.md)
and reproducible compatibility checks for the public fixed-dimensional result.
It is separate from the frozen manuscript repository. It is not a Prove2Me
node package.

The paper and original formalization remain in the separate
[frozen v1.0.0 release](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/releases/tag/v1.0.0).
The compatibility harness reads precisely 54 Lean source files from
[commit 1e73a12ff1076dd11affadbf619ddbbef587133e](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/tree/1e73a12ff1076dd11affadbf619ddbbef587133e/lean-fixed670).
The frozen release is archived as [DOI 10.5281/zenodo.23329194](https://doi.org/10.5281/zenodo.23329194).
This repository neither changes that release nor copies the paper into this one.

## The theorem's scope

For every natural number n at least 68000, the theorem constructs n injectively
indexed points in the single fixed Euclidean space R^458999. Distances between
distinct points are at least one; distances attached to different unordered
non-diagonal pairs differ by at least one; and every pair distance and the
diameter are strictly below (37/50)n². These are explicit sufficient bounds,
not claims of optimal dimension, threshold, coefficient, or priority.

## Palomar project and current evidence

The standalone project is `palomar/`. Its 54 proof modules, Solution, final
axiom audit, and intact sandboxed Comparator passed in
[hosted job 115100254416](https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/38337326194/job/115100254416).
The same [run 38337326194](https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/38337326194)
also passed Prove2Me's 54-module build and final axiom audit. The checked harness
commit was `7f7c0d588f7510c59d44757ee8d4e41b545009cc`.
Every published proof/configuration byte matches that Palomar job's recorded hashes.
The additional metadata and documentation have been validated separately.
The immutable submission snapshot `5510ffd94156d48dbe393ac619586b935212da79`
subsequently passed the [complete official preflight](https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/38340299337)
and [Palomar production verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/38342636995),
checked at 2026-10-13 03:44:33 UTC. con-ron, NanoDa and the default Lean kernel
accepted the solution. These are mechanical results; no editorial or registration
outcome is inferred from them. The selected source remains that exact immutable
commit even as this verification repository gains separate tooling.

Submission selection is `project_path=palomar`, with repository-relative
Comparator path `palomar/comparator.json`, metadata
`palomar/formalization.yaml`, and the exact immutable published commit.
The submission records the responsible human maintainer relationship separately
from mechanical proof verification.
The sole repository-root license is MIT. Other live Lean sources are absent;
harness templates end in `.lean.txt`.

## Two separate checks

- Palomar compatibility: Lean 4.35.0-rc2, Mathlib
  065356127b1dc0016f66b7283ce0ce2c4055aa55. The deterministic adapter adds module
  syntax and public imports/sections, then applies exactly three recorded
  compatibility edits. It builds all 54 modules and Solution, checks the final
  theorem's axioms, and runs the intact official `lake comparator` sandbox.
- Prove2Me compatibility: Lean 4.33.1, Mathlib
  0df444a360eaa60ab8c11dca51a86af692955474. It applies the same explicit
  linear-combination proof-step repair used by the Palomar port; the other 53
  sources are unchanged. `autoImplicit = false` is enabled, and the job builds every source module
  and checks the final theorem's axioms. It does not import or upload a node.

The permitted axioms are propext, Quot.sound, and Classical.choice. The Palomar
Challenge template contains one deliberate proof hole defining the statement
Comparator must match. Challenge alone is not a proof; Solution imports the
substantive development and never imports Challenge.

See the individual workflow step outcomes and logs for actual results. Each pass
establishes only the checks that ran. The separate complete Palomar runs establish
their recorded independent-kernel checks. None of these mechanical results implies
editorial acceptance, independent mathematical review, priority or journal acceptance.

## Official Palomar full preflight

Palomar's [agent intake instructions](https://submit.palomar-registry.org/llms.txt)
require its complete reusable workflow before intake. The standalone compatibility
checks above do not replace that gate. `palomar-full-preflight.yml` calls the
unmodified official workflow at commit
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, using `mode: full` and the
`palomar-standard-v1` GitHub-hosted runner profile. Dispatch it manually with the
exact public source commit intended for submission. It does not run on pushes.

That official workflow includes protected canonical-Challenge compilation,
source-provenance checks, sandboxed proof export and independent kernel replay.
Its mechanical report must say `status: pass` before intake. This gate passed for
`5510ffd94156d48dbe393ac619586b935212da79` in the linked complete preflight,
with `stage: complete` and all three kernels accepting. The report has no
mechanical errors or warnings; ordinary Lean style/deprecation warnings remain
in compiler output. Metadata inside the frozen package records its earlier
preparation-time status, rather than a later registry outcome.

Unlike the compatibility harness, the upstream workflow writes a Bundler cache
and uploads its bounded mechanical report with 90-day retention. Its standard
public runner compute is free, but storage allowances and paid-usage controls
must be checked before dispatch. On a restricted runner, its installer adds a
path-specific AppArmor rule allowing user namespaces for its pinned bubblewrap
binary. It also removes selected preinstalled SDKs and Docker images from the
disposable VM. These official behaviors require explicit execution approval.
The official profile's resource checks and sandbox must remain enabled. No secrets are inherited and repository permissions
are read-only. This preflight does not submit, perform editorial review, or
register a result.

## Prove2Me declaration extraction

[The separate extraction tools](extraction/README.md) prepare actual dependency,
type and source-position facts from the same Lean 4.33.1 compatibility copy.
The new extraction workflow is manual-only and binds both its own commit and the
frozen `5510ffd94156d48dbe393ac619586b935212da79` compatibility harness.
It repeats the build and axiom gates in its disposable runtime before extraction.
Successful extraction is distinct from transformed-node verification or a platform
submission. Inspect its exact phase results and bounded artifact before using any
generated facts; Python tests alone are not extraction evidence.

This additional workflow proposes one validated, source-derived artifact capped
at 64 MiB uncompressed with one-day retention, after verifying included storage
headroom and paid-overage blocking. Its public code and ordinary logs have
separate retention. The existing two compatibility jobs retain their original
no-artifact behavior and also rerun when the root integrity manifest changes.

## Reproducibility and runtime boundaries

SOURCE_MANIFEST.json contains every original and candidate source SHA256.
PALOMAR_MIGRATION_PATCHES.json records the three exact edits, reasons and platform scopes; its first proof-step repair is shared with Prove2Me.
FIXTURE_SHA256.json covers the minimal source/configuration templates; Lean
templates end in `.lean.txt`. Generated test candidates contain only the 54
proof files and the platform's allowlisted Lean/configuration/license files.
The separately published `palomar/` tree also contains its reviewed submission
metadata and source inventory. Manuscript files, private reports and prebuilt proof objects are omitted.
The independent extraction adapter is included separately; the official Prove2Me
scripts are fetched only for ephemeral documented use and are not vendored or relicensed.

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
