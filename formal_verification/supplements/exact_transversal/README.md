# Exact transversal — isolated new supplement

This is additional formal source, outside the unchanged 550-file primary project.
The completed default run has status
`FRESH_EXACT_TRANSVERSAL_SUPPLEMENT_VERIFIED`, with
`exhaustion_discharged: true`. It finished at 2026-10-10 18:46:00 UTC
(2026-10-11 02:46:00 Asia/Shanghai). The two theorem modules and audit were
freshly compiled; all three commands exited zero. The all-declaration audit
checks **49 declarations (32 theorems)** and permits only `propext`,
`Classical.choice` and `Quot.sound`. The report binds the final primary report
and all 544 imported primary source/artifact identities.

The earlier `evidence/conditional_build_run.json` is retained as an intermediate
snapshot: 47 declarations/30 theorems, with `TerminalExhaustion h` still a premise.
Its 18 imported primary modules and artifact hashes are recorded separately.
The independent source review preserves that earlier scope; the later completed
bridge is covered by `docs/strict_final_review_addendum.md` at the submission root.

The lower bound is unconditional: `hitting_lower_bound` and
`standard_hitting_lower_bound` prove that every list of physical/numerical cells
hitting all original induced ordered copies has length at least `2^h`.
The upper bound uses terminal classification to show that the list of leaf
diagonal cells hits every original copy and has length `2^h`. This list is
proved duplicate-free. Thus the attained-upper/universal-lower theorem pair
expresses precisely the usual finite-set transversal minimum, without relying
on an unspecified infimum or counting repeated cells as distinct set elements.
Both physical and ordinary `Fin(hostSize h)` matrix versions are included.

The packing uses one type-I physical copy per p. Each selected row itself
recovers p (marker/dummy offset p; leaf node p), which proves cell disjointness.
The parent-column offset is p mod 2 in its two-point parent block. All copies
are checked against the existing ordered-copy predicate with all 16 entries.

`ExactTransversalMain.lean` is the small final bridge, supplying
`classification_exhaustive h hh` from the completed primary global theorem.
It has now actually compiled, with its audit, after the primary build completed.
The conditional report alone does not certify this bridge. Reproduce from the
submission root:

```sh
python3 supplements/exact_transversal/scripts/build_and_audit.py \
  --primary-root "$PWD" \
  --lean /path/to/lean-4.24.0/bin/lean
```

The successful final run wrote `evidence/unconditional_build_run.json` with status
`FRESH_EXACT_TRANSVERSAL_SUPPLEMENT_VERIFIED`, `exhaustion_discharged: true`, and a
bound `unconditional_axiom_audit.json`. Only that state certifies the unconditional
`exact_physical_transversal` and `exact_standard_transversal` theorems. The actual
record, source hashes and bound audit provide that evidence.
The script explicitly rejects a pending primary build in its default mode.

The optional `--conditional-only` mode reproduces the intermediate proof; it
cannot issue an unconditional success status. All supplement build outputs live
under this directory's `.lake/build`, never in the primary library build tree.
No proof holes, project axioms, native evaluation, or prior H4 artifacts are used.
This is a direct classification corollary and makes no claim that the distinction
between hitting and removal, or its mechanism, originates here.
