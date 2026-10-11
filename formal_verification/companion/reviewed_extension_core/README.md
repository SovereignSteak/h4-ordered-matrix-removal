# Independently rebuilt extension core (derived project)

This directory is a deliberately separate, source-preserving extraction from
`../formalized_extensions`. It compiles the complete dependency closure of three
extension modules without requiring the original companion's 72 unrelated global
BV/LRAT certificate modules. The original companion files are unchanged.

## Verified result

The 2026-10-10 fresh run passed: 34 library modules plus the audit compiled in
198.22 seconds. The complete included declaration closure contains 1,570
declarations (991 theorems) and only the three standard axioms. The machine-readable
result is `evidence/extension_build_run.json`; the all-declaration audit is
`evidence/extension_axiom_audit.json`. This certifies this isolated core only.

## Exact scope

- GeneralPhysicalCompression: twin-free physical/indexed pattern witnesses at
  depth `1 <= d <= 6*k`, and the equivalent bounded family-freeness statements.
- MarkerPermutation: the arbitrary-edit lower bound under separately permuted
  marker modes, and the corresponding concrete-index/minimum-distance bounds.
- GeneralPhysicalCounting: block-fiber cardinalities and the exact multiplicative
  number of physical lifts of a prescribed valid quotient tuple.

Every declaration, statement and proof body in these three original modules is
byte-identical here; only their imports change. This is not a fresh build of the
full companion project and does not independently compile its global H4
classification, exact repair, exact copy-count, or removal-obstruction route.
It adds no theorem asserting `d <= h` to the existing extension interface.

## Why the split is necessary

The original import path is
`PhysicalHost -> TerminalClassification -> CertificateBridge -> CertifiedQueries`.
The actual general extension proofs do not require the 72 certified fixed queries,
but Lean loads every declaration in imported modules. Two unrelated arithmetic
regression modules also use `native_decide`, so auditing every imported declaration
would not have the same standard-three-axiom scope as auditing only the exported
extension theorems.

The derived project therefore copies unchanged declarations into:

- `PhysicalHostCore`: physical definitions and quotient correspondence, before the
  last two all-depth global-classification/repair theorems.
- `IndexedMatrixCore`: generic numeric matrix/indexing/count/edit interfaces, before
  theorem-specific global repair/count integrations.
- `TerminalTypes`: only the terminal-mode and terminal-form definitions.
- `HostSizes`: only branch factor, side length, canonical-repair size and its power identity.
- `FiniteMultiplicity`: only the block-multiplicity definition.

All remaining required modules are copied exactly, or have imports alone replaced.
`evidence/source_provenance.json` binds each file to the original SHA-256 and records
extraction boundaries. `evidence/import_refactor.diff` records every source change.
No proof is replaced with an assumption, weakened statement, numerical experiment,
`native_decide`, or precompiled H4Formal artifact.

## Reproduce the fresh build

Use Lean 4.24.0 and the external library revisions pinned in `lake-manifest.json`.
The helper accepts a `.lake/packages` directory with those revisions and their
matching official dependency artifacts. It never reads the main project's
H4Formal build path. For the parent submission layout:

```bash
python3 scripts/build_and_audit.py --clean \
  --lean /path/to/lean-4.24.0/bin/lean \
  --dependency-root ../../.lake/packages
```

For a standalone checkout, retrieve the pinned dependencies with Lake, obtain the
official mathlib cache, then give this helper that checkout's `.lake/packages`.
The `--clean` flag removes only this derived project's `.lake/build`, then compiles
all included project modules sequentially with `-j1`. `ExtensionAudit.lean` selects
all declarations by defining module, including private/anonymous declarations and
definitions, and rejects every axiom outside `propext`, `Classical.choice`, and
`Quot.sound`. All nine required exported theorems must exist as compiled theorems.

The definitive result is `evidence/extension_build_run.json`; do not infer successful
verification from source presence, this README, or an unfinished build log.
