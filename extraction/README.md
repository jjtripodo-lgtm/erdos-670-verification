# Prove2Me declaration extraction

## Version scope

These tools and fixtures verify the archived v1.0.0 theorem
(n ≥ 68000, dimension 458999, diameter < (37/50)n²).
The [current finite result](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension)
has its own [66-module proof](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/tree/f1604c368efce996a9af4d46f581e676e49054f5/lean)
for n ≥ 36354, dimension 81794, and diameter < (147/200)n².
The version-specific checks below do not verify those revised constants.

This is a preparation tool for the already-public fixed-dimensional Erdős 670
formalization. It extracts declaration dependencies and source-position facts.
It does not call Prove2Me, upload a node, generate a transformed proof, or certify
platform acceptance.

## Exact inputs

- Original theorem source: `jjtripodo-lgtm/erdos-670-fixed-dimension` at
  `1e73a12ff1076dd11affadbf619ddbbef587133e`
- Compatibility harness: this repository at
  `5510ffd94156d48dbe393ac619586b935212da79`
- Candidate: Lean 4.33.1, Mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474`, `autoImplicit=false`
- All 54 source modules participate. The compatibility copy has 53 unchanged
  sources and the single recorded PrefixSums proof-step repair
- Official extraction methodology and tools:
  [prove2me_workspace at 78989800ba0b3149ee34205257025bd0f617e8ef](https://github.com/prove2me/prove2me_workspace/blob/78989800ba0b3149ee34205257025bd0f617e8ef/references/upload_full_project.md)

The new wrapper and the frozen compatibility harness are fetched separately at
exact Git commits. The submitted Palomar snapshot remains the immutable
`5510ffd94156d48dbe393ac619586b935212da79`; no extraction run alters it.

## Evidence boundaries

The candidate's 54-module build and target axiom audit already passed in
[run 38339656019](https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/38339656019).
Its disposable VM was not retained. Therefore the extraction job recreates the
same candidate and repeats those gates before reusing its newly built objects
for serial extraction. It reads the targeted canonical Mathlib cache rather
than repeating an unrelated source-only Mathlib rebuild.

Python tests and static workflow checks do not prove that the companion Lean
programs compile or that the real extraction succeeds. The actual run must
complete every extraction stage, pass the export checks, and successfully retain
its artifact. A green original compatibility build alone is insufficient. A
skipped extraction job, including a false storage-confirmation input, is not a
successful extraction.

Even successful extraction leaves transformed-node generation, exact staged
compilation, theorem-type comparison, axiom audits, import isolation and any
platform submission unfinished. Each later result needs its own evidence.

## Manual execution and resources

`prove2me-extraction.yml` is manual-only and uses one standard public
`ubuntu-22.04` job. Repository permissions are read-only. There are no repository
secrets, private fetches, platform API calls, paid runner labels, security-setting
changes or reusable GitHub-cache writes.

The owner must verify at least 128 MiB of included storage headroom and
an effective block on paid overage before setting `storage_guard_confirmed`.
That input records an external verification; the workflow cannot inspect billing
and does not change account settings. This includes margin beyond the 64 MiB
source-data cap for archive overhead and ordinary logs. If that gate cannot be established, do
not dispatch. Standard public runner compute is free, while
[artifact storage has separate allowances](https://docs.github.com/en/billing/concepts/product-billing/github-actions).

The job requires at least 16 GiB of initially free workspace and leaves the
adapter's 8 GiB disk and 1.5 GiB available-memory floors intact. It does not
remove unrelated runner files to make room. Extraction is serial and the whole
job is limited to 180 minutes. A capacity failure is a blocker, never a pass.

Publishing the reviewed files and refreshed root integrity manifest also
triggers this repository's two existing compatibility jobs. Those jobs retain
their existing no-artifact/no-reusable-GitHub-cache behavior. They do not trigger
the new extraction job.

## Public artifact contents and retention

Only a successful extraction can create the upload staging directory. It must
have an exact allowlist, validated schemas, matching hashes, no symlinks or
special files, and at most 64 MiB total uncompressed data.

Proposed artifact categories, requiring explicit owner approval, are:

- The 54 already-public MIT source files, their MIT license and necessary
  source/configuration provenance
- Declaration graphs, statement types, parser/reference positions and exact
  private-name mappings derived from those public sources
- Sanitized phase, runtime and integrity receipts with relative paths

The manuscript, upstream extractor programs or diffs, dependency sources,
toolchains, compiled objects, raw diagnostics, environment dumps and credentials
are excluded. The official scripts are fetched with exact SHA-256 checks for
ephemeral use under their documented methodology; no broad redistribution
license is claimed. Independently authored companions are separate from those
scripts. Companion Lean templates use `.lean.txt` in this repository and are
materialized only in the disposable workspace.

The pinned official upload action retains one artifact for one day. Anyone with
GitHub read access to this public repository can download it. Public code and
ordinary run logs have separate retention and do not expire with that artifact.
Download and verify the artifact promptly if it is needed for further private
planning. Artifact ID, URL and ZIP digest appear in the job summary.

No registration, Prove2Me upload or account operation is authorized by these
tools or by a successful extraction.
