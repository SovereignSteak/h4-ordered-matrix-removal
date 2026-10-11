# Formal verification package

This archive contains all retained primary Lean source files, the exact
dependency lock, the isolated extension core, and the exact-transversal
supplement. It omits the historical second companion's global LRAT route,
72 independent BV/LRAT certificate modules, incoming drafts, and redundant
review logs, none of which is imported by the primary H4Formal project or
the isolated extension project.

## Rebuilding

Requires Lean 4.24.0 (via elan), Lake, Python 3, and network access for
the pinned mathlib dependencies. Run from this directory:

    bash verify_all.sh

Manual equivalent for the main theorem:

    lake exe cache get
    lake build H4Formal
    lake env lean Audit.lean
    lake env lean ProofAudit.lean

The two isolated supplemental projects are then checked by verify_all.sh
and have their own build scripts and reports. The exact-transversal bridge
imports the main project and therefore must run after lake build.

An evidence/ directory contains selected previous compilation/audit outputs
from the supplied 2026-10-11 release. These are historical build records,
not claims that a new build has completed on a recipient's computer.
The verification script explicitly runs fresh checks upon invocation.

The isolated structural extension project retains the proven three-module
interface, dependency-closure extraction, source provenance, and compiled
axiom audit. The original full alternative certificate route is excluded
to keep the distribution focused and avoid conflating proof systems.

All source files copied from the supplied archive are byte-identical.
The included manifest records SHA-256 hashes of this split distribution.
