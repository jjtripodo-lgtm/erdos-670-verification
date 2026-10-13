# Extraction adapter

See [the extraction overview](../README.md) for the immutable source pins,
execution and publication boundaries, resource limits, and remaining node checks.
This directory contains independently authored Python support and two Lean
companion templates. It does not contain the upstream extractor programs.

## Execution contract

The candidate must already have passed the frozen compatibility harness's
54-module build and target axiom audit. The adapter refuses to install anything
or rebuild missing objects. It verifies every participating source, fixed
configuration/license hashes, native Lean 4.33.1, and clean pinned dependencies.

The hosted workflow supplies this command:

```sh
python3 extraction/adapter/run_extraction.py \
  --project "$RUNNER_TEMP/candidate" \
  --manifest "$RUNNER_TEMP/verifier/SOURCE_MANIFEST.json" \
  --extractors "$RUNNER_TEMP/prove2me-upstream" \
  --toolchain-bin "$RUNNER_TEMP/toolchain/lean-4.33.1-linux/bin" \
  --output "$RUNNER_TEMP/prove2me-extraction" \
  --wrapper-commit "$GITHUB_SHA" \
  --harness-commit 5510ffd94156d48dbe393ac619586b935212da79 \
  --workflow-run-url "https://github.com/jjtripodo-lgtm/erdos-670-verification/actions/runs/$GITHUB_RUN_ID" \
  --execute --resources-coordinated
```

The output directory must be new and outside the candidate. Lean search paths
are captured through the native Lake environment and made absolute; the actual
Lean processes run in a separate working directory. Stage 1 can therefore use
its original output filename without changing the candidate tree.

Official Stage 1 receives only the two documented root-import/project-prefix
edits. Official Stage 2 remains byte-identical. Independent companions produce
constructor/type facts and parser/binding/private-name facts. The source
companion uses `autoImplicit=false`; its resolved references and byte ranges
must agree with the unchanged official oracle. Disagreement fails the run.

There are 110 serial Lean invocations: Stage 1, environment facts, and two
source passes for each module. Source/configuration/tool stability is checked
throughout. Resource floors are 8 GiB free disk and 1.5 GiB available RAM, with
one CPU and Lean worker, a 30-minute per-command limit, 16 MiB per file, and a
64 MiB final uncompressed artifact ceiling.

## Validated output only

Only complete successful extraction creates `OUTPUT/artifact/`. The exact
filename allowlist includes all 54 public sources and MIT LICENSE, dependency
and type facts, parser/reference facts, private-name mappings, and sanitized
provenance receipts. It excludes tool code, dependencies, objects and raw logs.
Links, special files, unexpected paths/fields, incomplete coverage, false
success flags, hash drift and cap violations fail validation.

The same independent export check runs again immediately before upload:

```sh
python3 extraction/adapter/export_artifact.py "$RUNNER_TEMP/prove2me-extraction/artifact"
```

Failed runs produce no upload-eligible artifact. Ordinary job output may include
an at-most-8-KiB failure summary with phase/exit/hash information and bounded
error headers from the independent companions or public project. It excludes
source excerpts, arbitrary raw diagnostics and absolute runtime paths.

## Tests and later theorem checks

The tests require the exact two upstream files in an ephemeral directory:

```sh
PROVE2ME_TEST_EXTRACTORS=/ephemeral/pinned-tools \
  python3 -m unittest discover -s extraction/adapter -p 'test_*.py' -v
```

Synthetic tests and Python syntax checks do not compile the Lean companions
or produce actual source facts. Inspect the hosted phase results separately.

The optional `make_type_probe.py` and `compare_type_dumps.py` support later
checks after transformed modules exist. They compare explicit pairs of
pretty-printed theorem types without normalizing away differences. They do not
generate nodes, compile proofs, establish complete coverage, audit axioms or
authorize any platform upload. Those remain separate required gates.
