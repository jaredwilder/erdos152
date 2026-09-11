# erdos152

**Lean 4 formalizations of the statements of 160 open Erdős problems** - one of the larger
statement corpora for this problem set anywhere. The full defect audit ships with it, including
the 72 the gate rejected.

Author: Jared Wilder. First public timestamp: 2026-09-10.

## What this is

Each file contains:

- the verbatim source text of the problem, frozen in a comment block, with the accession date
- Lean definitions encoding the objects the problem talks about
- a `def erdosProblemN : Prop` stating the problem itself
- a decidable finite analogue of the problem
- two small proved lemmas, `witness_pos` and `witness_neg`, showing that the finite analogue is
  neither vacuous nor trivially true
- the main theorem, which is almost always `by sorry`

## What this is not

**These are not proofs, and nothing here closes any Erdős problem.**

Of the 160 files, 1 has a fully proved main statement. The other 159 end in `sorry`. Anyone
reading a claim to the contrary anywhere should check `MANIFEST.json`, which records, per file,
every declared theorem and which of them are unproved.

## The defect audit, which is included on purpose

Every file was run through a 33-blade semantic certification gate that checks whether the Lean
statement still means what the source text said. The gate grades on a five rung ladder:
KERNEL_VALID, MODEL_COHERENT, SOURCE_SUBQUESTION_VALID, SOURCE_EQUIVALENT,
CURRENT_SOURCE_EQUIVALENT.

Results over this corpus:

| outcome | count |
|---|---|
| files | 160 |
| reached CERTIFIED | **0** |
| rejected on at least one blade | 72 |
| zero blade convictions and a frozen source statement | 46 |
| ladder level reached, all files | KERNEL_VALID (rung 1 of 5) |

An earlier independent audit of 126 of these targets found 11 formally false statements, 11 where
the open content had been erased, 4 malformed, and 5 that proved a neighboring problem rather than
the stated one. The gate independently caught 58 of 58 of the artifacts that audit condemned.

**The rejected files are shipped here, labeled, rather than removed.** A formalization corpus with
its failures deleted cannot be used to study semantic drift, and semantic drift is the open problem
in autoformalization. The failures are the part of this release with research value.

## How to check any of it yourself

- `MANIFEST.json` carries a sha256 for every file, the list of theorems it declares, which are
  unproved, and the gate verdict.
- Every `.lean` file compiles against Mathlib on its own. Nothing here depends on the author's
  toolchain.
- The source text is in the file, with the date it was accessed, so a reader can compare the
  formal statement against the original without leaving the file.

## Status table

| problem | file | main statement | gate verdict | blades fired | source IR |
|---|---|---|---|---|---|
| 1 | `lean/erdos-1.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 3 | `lean/erdos-3.lean` | `sorry` | BLOCKED | none | FROZEN |
| 10 | `lean/erdos-10.lean` | `sorry` | BLOCKED | none | FROZEN |
| 11 | `lean/erdos-11.lean` | `sorry` | BLOCKED | none | FROZEN |
| 12 | `lean/erdos-12.lean` | `sorry` | REJECTED_SEMANTIC | B29 | FROZEN |
| 14 | `lean/erdos-14.lean` | `sorry` | REJECTED_SEMANTIC | B28 | FROZEN |
| 15 | `lean/erdos-15.lean` | `sorry` | BLOCKED | none | FROZEN |
| 21 | `lean/erdos-21.lean` | `sorry` | BLOCKED | none | FROZEN |
| 28 | `lean/erdos-28.lean` | `sorry` | REJECTED_SEMANTIC | B28 | FROZEN |
| 30 | `lean/erdos-30.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 32 | `lean/erdos-32.lean` | `sorry` | BLOCKED | none | FROZEN |
| 33 | `lean/erdos-33.lean` | `sorry` | REJECTED_SEMANTIC | B16 | FROZEN |
| 50 | `lean/erdos-50.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 51 | `lean/erdos-51.lean` | `sorry` | BLOCKED | none | FROZEN |
| 52 | `lean/erdos-52.lean` | `sorry` | BLOCKED | none | FROZEN |
| 60 | `lean/erdos-60.lean` | `sorry` | REJECTED_SEMANTIC | B04, B07, B08, B24, B28 | FROZEN |
| 62 | `lean/erdos-62.lean` | `sorry` | REJECTED_SEMANTIC | B08, B21, B30 | FROZEN |
| 65 | `lean/erdos-65.lean` | `sorry` | REJECTED_SEMANTIC | B06, B08, B24, B28 | FROZEN |
| 68 | `lean/erdos-68.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 77 | `lean/erdos-77.lean` | `sorry` | REJECTED_SEMANTIC | B26 | FROZEN |
| 82 | `lean/erdos-82.lean` | `sorry` | BLOCKED | none | FROZEN |
| 87 | `lean/erdos-87.lean` | `sorry` | REJECTED_SEMANTIC | B05, B13, B30 | FROZEN |
| 89 | `lean/erdos-89.lean` | `sorry` | REJECTED_SEMANTIC | B13 | FROZEN |
| 100 | `lean/erdos-100.lean` | `sorry` | REJECTED_SEMANTIC | B21, B30 | FROZEN |
| 101 | `lean/erdos-101.lean` | `sorry` | REJECTED_SEMANTIC | B21, B30 | FROZEN |
| 103 | `lean/erdos-103.lean` | `sorry` | REJECTED_SEMANTIC | B19, B24 | FROZEN |
| 110 | `lean/erdos-110.lean` | `sorry` | BLOCKED | none | FROZEN |
| 112 | `lean/erdos-112.lean` | `sorry` | REJECTED_SEMANTIC | B05, B08, B09, B16, B24 | FROZEN |
| 116 | `lean/erdos-116.lean` | PROVED | BLOCKED | none | PROVISIONAL |
| 119 | `lean/erdos-119.lean` | `sorry` | BLOCKED | none | FROZEN |
| 120 | `lean/erdos-120.lean` | `sorry` | REJECTED_SEMANTIC | B09, B10, B30 | FROZEN |
| 129 | `lean/erdos-129.lean` | `sorry` | BLOCKED | none | FROZEN |
| 131 | `lean/erdos-131.lean` | `sorry` | REJECTED_SEMANTIC | B13, B28, B29, B30 | PROVISIONAL |
| 138 | `lean/erdos-138.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 145 | `lean/erdos-145.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 146 | `lean/erdos-146.lean` | `sorry` | REJECTED_SEMANTIC | B05 | PROVISIONAL |
| 148 | `lean/erdos-148.lean` | `sorry` | REJECTED_SEMANTIC | B13, B16 | FROZEN |
| 149 | `lean/erdos-149.lean` | `sorry` | REJECTED_SEMANTIC | B29 | PROVISIONAL |
| 151 | `lean/erdos-151.lean` | `sorry` | BLOCKED | none | FROZEN |
| 156 | `lean/erdos-156.lean` | `sorry` | REJECTED_SEMANTIC | B08, B09, B24 | FROZEN |
| 159 | `lean/erdos-159.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 160 | `lean/erdos-160.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 165 | `lean/erdos-165.lean` | `sorry` | REJECTED_SEMANTIC | B04, B05, B08, B26, B28 | PROVISIONAL |
| 168 | `lean/erdos-168.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 172 | `lean/erdos-172.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 174 | `lean/erdos-174.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 179 | `lean/erdos-179.lean` | `sorry` | REJECTED_SEMANTIC | B29 | FROZEN |
| 181 | `lean/erdos-181.lean` | `sorry` | BLOCKED | none | FROZEN |
| 182 | `lean/erdos-182.lean` | `sorry` | REJECTED_SEMANTIC | B28 | FROZEN |
| 184 | `lean/erdos-184.lean` | `sorry` | BLOCKED | none | FROZEN |
| 186 | `lean/erdos-186.lean` | `sorry` | REJECTED_SEMANTIC | B13, B16 | PROVISIONAL |
| 187 | `lean/erdos-187.lean` | `sorry` | REJECTED_SEMANTIC | B19, B23, B28 | FROZEN |
| 190 | `lean/erdos-190.lean` | `sorry` | REJECTED_SEMANTIC | B03 | PROVISIONAL |
| 197 | `lean/erdos-197.lean` | `sorry` | BLOCKED | none | FROZEN |
| 200 | `lean/erdos-200.lean` | `sorry` | BLOCKED | none | FROZEN |
| 208 | `lean/erdos-208.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 215 | `lean/erdos-215.lean` | `sorry` | BLOCKED | none | FROZEN |
| 217 | `lean/erdos-217.lean` | `sorry` | REJECTED_SEMANTIC | B30 | FROZEN |
| 218 | `lean/erdos-218.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 234 | `lean/erdos-234.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 236 | `lean/erdos-236.lean` | `sorry` | BLOCKED | none | FROZEN |
| 243 | `lean/erdos-243.lean` | `sorry` | BLOCKED | none | FROZEN |
| 244 | `lean/erdos-244.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 247 | `lean/erdos-247.lean` | `sorry` | BLOCKED | none | FROZEN |
| 249 | `lean/erdos-249.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 251 | `lean/erdos-251.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 260 | `lean/erdos-260.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 269 | `lean/erdos-269.lean` | `sorry` | REJECTED_SEMANTIC | B29 | FROZEN |
| 288 | `lean/erdos-288.lean` | `sorry` | BLOCKED | none | FROZEN |
| 293 | `lean/erdos-293.lean` | `sorry` | REJECTED_SEMANTIC | B01, B04, B13, B26, B28 | FROZEN |
| 319 | `lean/erdos-319.lean` | `sorry` | REJECTED_SEMANTIC | B16 | PROVISIONAL |
| 334 | `lean/erdos-334.lean` | `sorry` | BLOCKED | none | FROZEN |
| 357 | `lean/erdos-357.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 368 | `lean/erdos-368.lean` | `sorry` | REJECTED_SEMANTIC | B11, B28 | FROZEN |
| 376 | `lean/erdos-376.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 382 | `lean/erdos-382.lean` | `sorry` | BLOCKED | none | FROZEN |
| 383 | `lean/erdos-383.lean` | `sorry` | BLOCKED | none | FROZEN |
| 385 | `lean/erdos-385.lean` | `sorry` | BLOCKED | none | FROZEN |
| 389 | `lean/erdos-389.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 390 | `lean/erdos-390.lean` | `sorry` | REJECTED_SEMANTIC | B26 | PROVISIONAL |
| 409 | `lean/erdos-409.lean` | `sorry` | REJECTED_SEMANTIC | B28, B29 | PROVISIONAL |
| 411 | `lean/erdos-411.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 414 | `lean/erdos-414.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 415 | `lean/erdos-415.lean` | `sorry` | REJECTED_SEMANTIC | B04, B09, B13, B28, B29, B30 | PROVISIONAL |
| 416 | `lean/erdos-416.lean` | `sorry` | REJECTED_SEMANTIC | B28, B29 | PROVISIONAL |
| 436 | `lean/erdos-436.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 450 | `lean/erdos-450.lean` | `sorry` | REJECTED_SEMANTIC | B02, B28 | FROZEN |
| 451 | `lean/erdos-451.lean` | `sorry` | BLOCKED | none | FROZEN |
| 470 | `lean/erdos-470.lean` | `sorry` | REJECTED_SEMANTIC | B13, B18, B30 | PROVISIONAL |
| 479 | `lean/erdos-479.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 503 | `lean/erdos-503.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 510 | `lean/erdos-510.lean` | `sorry` | BLOCKED | none | FROZEN |
| 528 | `lean/erdos-528.lean` | `sorry` | REJECTED_SEMANTIC | B09, B13, B28 | PROVISIONAL |
| 530 | `lean/erdos-530.lean` | `sorry` | REJECTED_SEMANTIC | B04, B21, B30 | PROVISIONAL |
| 531 | `lean/erdos-531.lean` | `sorry` | REJECTED_SEMANTIC | B04, B05, B08, B26, B28 | FROZEN |
| 536 | `lean/erdos-536.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 544 | `lean/erdos-544.lean` | `sorry` | REJECTED_SEMANTIC | B09, B14, B24, B30 | PROVISIONAL |
| 557 | `lean/erdos-557.lean` | `sorry` | BLOCKED | none | FROZEN |
| 560 | `lean/erdos-560.lean` | `sorry` | REJECTED_SEMANTIC | B01, B04, B07, B08, B09, B12, B13, B28 | FROZEN |
| 562 | `lean/erdos-562.lean` | `sorry` | BLOCKED | none | FROZEN |
| 564 | `lean/erdos-564.lean` | `sorry` | BLOCKED | none | FROZEN |
| 569 | `lean/erdos-569.lean` | `sorry` | BLOCKED | none | FROZEN |
| 571 | `lean/erdos-571.lean` | `sorry` | REJECTED_SEMANTIC | B04, B07, B08, B09, B24, B28 | FROZEN |
| 593 | `lean/erdos-593.lean` | `sorry` | REJECTED_SEMANTIC | B28, B30 | FROZEN |
| 604 | `lean/erdos-604.lean` | `sorry` | REJECTED_SEMANTIC | B15, B21, B28, B30 | FROZEN |
| 612 | `lean/erdos-612.lean` | `sorry` | REJECTED_SEMANTIC | B29 | FROZEN |
| 616 | `lean/erdos-616.lean` | `sorry` | REJECTED_SEMANTIC | B08, B12, B13, B16, B28 | FROZEN |
| 653 | `lean/erdos-653.lean` | `sorry` | REJECTED_SEMANTIC | B28 | FROZEN |
| 670 | `lean/erdos-670.lean` | `sorry` | BLOCKED | none | FROZEN |
| 671 | `lean/erdos-671.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 679 | `lean/erdos-679.lean` | `sorry` | REJECTED_SEMANTIC | B03, B21, B28, B29, B30 | FROZEN |
| 711 | `lean/erdos-711.lean` | `sorry` | BLOCKED | none | FROZEN |
| 714 | `lean/erdos-714.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 724 | `lean/erdos-724.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 725 | `lean/erdos-725.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 726 | `lean/erdos-726.lean` | `sorry` | BLOCKED | none | FROZEN |
| 727 | `lean/erdos-727.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 730 | `lean/erdos-730.lean` | `sorry` | BLOCKED | none | FROZEN |
| 731 | `lean/erdos-731.lean` | `sorry` | REJECTED_SEMANTIC | B13, B22, B30 | FROZEN |
| 769 | `lean/erdos-769.lean` | `sorry` | REJECTED_SEMANTIC | B09, B24 | PROVISIONAL |
| 770 | `lean/erdos-770.lean` | `sorry` | REJECTED_SEMANTIC | B29 | PROVISIONAL |
| 787 | `lean/erdos-787.lean` | `sorry` | BLOCKED | none | FROZEN |
| 805 | `lean/erdos-805.lean` | `sorry` | REJECTED_SEMANTIC | B13 | FROZEN |
| 809 | `lean/erdos-809.lean` | `sorry` | REJECTED_SEMANTIC | B26 | FROZEN |
| 820 | `lean/erdos-820.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 836 | `lean/erdos-836.lean` | `sorry` | REJECTED_SEMANTIC | B08, B13, B28, B30 | FROZEN |
| 850 | `lean/erdos-850.lean` | `sorry` | REJECTED_SEMANTIC | B01 | FROZEN |
| 864 | `lean/erdos-864.lean` | `sorry` | REJECTED_SEMANTIC | B13 | PROVISIONAL |
| 866 | `lean/erdos-866.lean` | `sorry` | REJECTED_SEMANTIC | B04, B08, B09, B13, B24, B28 | FROZEN |
| 872 | `lean/erdos-872.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 885 | `lean/erdos-885.lean` | `sorry` | BLOCKED | none | FROZEN |
| 902 | `lean/erdos-902.lean` | `sorry` | REJECTED_SEMANTIC | B03, B04, B08, B09, B13, B26, B28 | FROZEN |
| 928 | `lean/erdos-928.lean` | `sorry` | REJECTED_SEMANTIC | B05 | PROVISIONAL |
| 929 | `lean/erdos-929.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 936 | `lean/erdos-936.lean` | `sorry` | REJECTED_SEMANTIC | B28 | PROVISIONAL |
| 943 | `lean/erdos-943.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 953 | `lean/erdos-953.lean` | `sorry` | REJECTED_SEMANTIC | B10 | FROZEN |
| 961 | `lean/erdos-961.lean` | `sorry` | REJECTED_SEMANTIC | B13, B26 | FROZEN |
| 963 | `lean/erdos-963.lean` | `sorry` | BLOCKED | none | FROZEN |
| 969 | `lean/erdos-969.lean` | `sorry` | BLOCKED | none | FROZEN |
| 975 | `lean/erdos-975.lean` | `sorry` | BLOCKED | none | FROZEN |
| 1003 | `lean/erdos-1003.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 1004 | `lean/erdos-1004.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 1009 | `lean/erdos-1009.lean` | `sorry` | BLOCKED | none | FROZEN |
| 1010 | `lean/erdos-1010.lean` | `sorry` | REJECTED_SEMANTIC | B08 | FROZEN |
| 1029 | `lean/erdos-1029.lean` | `sorry` | REJECTED_SEMANTIC | B26 | FROZEN |
| 1039 | `lean/erdos-1039.lean` | `sorry` | REJECTED_SEMANTIC | B29 | FROZEN |
| 1049 | `lean/erdos-1049.lean` | `sorry` | BLOCKED | none | FROZEN |
| 1065 | `lean/erdos-1065.lean` | `sorry` | REJECTED_SEMANTIC | B15 | FROZEN |
| 1066 | `lean/erdos-1066.lean` | `sorry` | REJECTED_SEMANTIC | B13, B16, B29 | FROZEN |
| 1070 | `lean/erdos-1070.lean` | `sorry` | BLOCKED | none | FROZEN |
| 1073 | `lean/erdos-1073.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 1085 | `lean/erdos-1085.lean` | `sorry` | REJECTED_SEMANTIC | B22, B30 | FROZEN |
| 1087 | `lean/erdos-1087.lean` | `sorry` | REJECTED_SEMANTIC | B21, B30 | FROZEN |
| 1135 | `lean/erdos-1135.lean` | `sorry` | BLOCKED | none | FROZEN |
| 1150 | `lean/erdos-1150.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 1158 | `lean/erdos-1158.lean` | `sorry` | REJECTED_SEMANTIC | B04, B08, B09, B12, B24, B28 | FROZEN |
| 1159 | `lean/erdos-1159.lean` | `sorry` | BLOCKED | none | FROZEN |
| 1160 | `lean/erdos-1160.lean` | `sorry` | BLOCKED | none | PROVISIONAL |
| 1171 | `lean/erdos-1171.lean` | `sorry` | REJECTED_SEMANTIC | B21, B30 | FROZEN |

## License

Apache-2.0, matching Mathlib. See LICENSE.

## Corrections

If a formalization here is wrong, it probably is: the audit above says so about a known subset and
may be incomplete about the rest. Open an issue. A statement that is wrong and labeled is more
useful than a statement that is wrong and quiet.
