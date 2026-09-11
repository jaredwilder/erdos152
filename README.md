# 160 Erdős problem statements formalized in Lean

A corpus of **160 Lean 4 formalizations of open Erdős problem statements**, each packaged with the source text, mathematical definitions, a finite test analogue, and small non-vacuity checks. The repository also ships a file-by-file semantic audit comparing the formal statements with their sources.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## What each file contains

Each formalization includes:

- the source problem text, frozen in a comment with its accession date;
- Lean definitions for the mathematical objects involved;
- a proposition `erdosProblemN : Prop` representing the problem statement;
- a decidable finite analogue for testing the encoding;
- small positive and negative witness lemmas showing that the finite analogue is not vacuous;
- the main problem statement in Lean.

This is primarily a **statement-formalization corpus**, not a proof corpus. Of the 160 files, **1 has a proved main statement and 159 leave the main statement as `sorry`**. That distinction is recorded explicitly in `MANIFEST.json`.

## Semantic audit

Formal correctness and source fidelity are different questions: Lean can accept a precisely stated theorem even when that theorem is not the one the source intended.

All 160 files were therefore run through 33 deterministic semantic checks covering issues such as changed domains, lost hypotheses, altered asymptotics, malformed object models, and neighboring-but-different statements.

| audit outcome | count |
|---|---:|
| files | **160** |
| rejected by at least one semantic check | **72** |
| no rejection, but insufficient information for the strongest comparison | **88** |
| independently known-bad artifacts detected | **58 of 58** |

A previous independent review of 126 targets found 11 formally false statements, 11 where the open content had effectively disappeared, 4 malformed formalizations, and 5 that encoded a neighboring problem. The semantic checker detected all 58 artifacts from that review that were classified as defective.

The rejected files remain in the repository. They are useful examples of how mathematical meaning can drift during formalization and provide a concrete corpus for improving source-to-Lean translation.

## How to inspect the corpus

`MANIFEST.json` is the machine-readable index. For every file it records:

- SHA-256;
- declared theorems;
- whether the main statement is proved or left as `sorry`;
- semantic-audit status;
- which checks fired;
- whether the source statement was frozen or provisional.

Every `.lean` file also contains the source text directly, so a mathematician can compare the English statement and the Lean proposition side by side without relying on the summary metadata.

The companion repository `jaredwilder/lean-semantic-blades` documents the 33 semantic checks and their validation history.

## Why publish failed formalizations?

Because they are part of the research object. A corpus containing only the successful encodings would hide exactly the failure modes that matter for mathematical autoformalization. Here, incorrect or incomplete statements remain visible with their audit status attached.

That does **not** make every unflagged file correct; it means the evidence needed to inspect each one is public.

## License

Apache-2.0, matching Mathlib. See `LICENSE`.

## Corrections

If a source comparison, Lean statement, or audit verdict is wrong, open an issue with the smallest reproducible discrepancy. Corrections should improve the record rather than erase the earlier artifact.