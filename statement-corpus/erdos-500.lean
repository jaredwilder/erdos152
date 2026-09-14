/-
# Erdős problem #500 — Turán's hypergraph problem $\mathrm{ex}_3(n,K_4^3)$  (**OPEN**, $500 prize)

## The question (verbatim from the frozen source, node `n000-question`)

> What is $\mathrm{ex}_3(n,K_4^3)$? That is, the largest number of $3$-edges which can placed on
> $n$ vertices so that there exists no $K_4^3$, a set of 4 vertices which is covered by all 4
> possible $3$-edges.

## The resolution node (verbatim, node `n001-resolution`)

> A problem of Tur\'{a}n. Tur\'{a}n observed that dividing the vertices into three equal parts
> $X_1,X_2,X_3$, and taking the edges to be those triples that either have exactly one vertex in
> each part or two vertices in $X_i$ and one vertex in $X_{i+1}$ (where $X_4=X_1$) shows that
> \[\mathrm{ex}_3(n,K_4^3)\geq\left(\frac{5}{9}+o(1)\right)\binom{n}{3}.\]
> This is probably the truth. The current best upper bound is
> \[\mathrm{ex}_3(n,K_4^3)\leq 0.5611666\binom{n}{3},\]
> due to Razborov \cite{Ra10}. See also [712] for the general case.

## What is formalized here — and what is deliberately NOT

**This problem is OPEN.**  This file states the QUESTION and asserts no answer to it.
`Erdos500.Question` is a `def ... : Prop` whose value `c` is existentially quantified and never
supplied.  There is no `erdos_500_resolution`.

Turán's `5/9` appears in exactly two places, both of them clearly labelled as *not* results:
`TuranConjecture`, a `def : Prop` (the source says "this is probably the truth" — a belief, not a
theorem), and inside `turan_lower_bound`, which is the **lower bound the source records as
established**, not the value.

What is stated as a `theorem` (each with `sorry`, each named after the author the source credits)
is only what the resolution node records as known:

* `turan_lower_bound` — $\mathrm{ex}_3(n,K_4^3)\geq(5/9+o(1))\binom n3$ (Turán).
* `turan_construction_free` / `turan_construction_card` — the two halves of Turán's explicit
  construction, which is the *reason* the lower bound holds and which the source spells out.
* `razborov_upper_bound` — $\mathrm{ex}_3(n,K_4^3)\leq 0.5611666\binom n3$ (Razborov, `Ra10`).
* `turan_density_lower` / `razborov_density_upper` — the same two facts phrased as bounds on the
  limiting density.  ⛔ These two are CONDITIONAL on a limit existing and are therefore vacuous
  if none does; see the next paragraph.  They are supplied because they are the shape in which
  both bounds are actually proved in the literature, and the unconditional `∀ᶠ n` forms above are
  supplied so that nothing in this file depends on the conditional shape.

⛔ **No sorried theorem asserts that the limit $\lim \mathrm{ex}_3(n,K_4^3)/\binom n3$ exists.**
It does — the ratio is non-increasing, by the standard averaging argument — but the source's
resolution node does not state that, and this file states only what its source states.  The
consequence is named rather than hidden: `Question` (which asserts existence of the limit) is
therefore **weaker than the open problem**, because existence is classical and only the VALUE is
open.  See "the gap between `Question` and the prize" below.

⛔ **`0.5611666` is NOT stated as `∀ n`.**  Read literally, the source's displayed inequality is
false at small `n`: `ex3 3 = 1 = choose 3 3` (PROVED below), so the ratio is `1` there, and
`ex3 4 = 3` (take three of the four triples; NOT formalized here), ratio `3/4`.  The density is non-increasing in `n` and starts at `1`, so any
constant upper bound below `1` can only be asymptotic.  Both bounds are therefore stated with an
explicit `ε` along `Filter.atTop`, which is what the `o(1)` in the source's *lower* bound already
signals for that direction.

## The gap between `Question` and the prize, named honestly

The source asks "What is $\mathrm{ex}_3(n,K_4^3)$?".  No `Prop` can demand a determination:
"compute this" is not a proposition.  The strongest statement about #500 that names no answer is
`∃ c, IsTuranDensity c` — the ratio converges to *something*.  That is strictly weaker than the
problem, and (unlike the sibling #712 case, where the same remark applies) it is weaker in a way
that matters here: existence of `c` is known.  What is open is `c`'s value, which is pinned down
only up to the interval `[5/9, 0.5611666]` by the two theorems below.  `IsTuranDensity` is
supplied as the parametric shape a resolution would take, and `turanDensity_unique` (PROVED)
records that it pins `c` uniquely, so "the value" is well posed.

## Representation, and why this shape

* **A `3`-edge is a `Finset (Fin n)` of card `3`**, and a 3-uniform hypergraph is
  `H : Finset (Finset (Fin n))` with `∀ e ∈ H, #e = 3` (`Is3Uniform`).
  ⛔ **Not a `Sym2`-like type.**  Mathlib's `Sym2 α` is the *unordered pair* type used for
  `SimpleGraph` edges; the `r = 3` analogue would be `Sym.Sym' α 3` or `Sym α 3`, which is a
  multiset of size 3 and therefore permits repeated vertices (`⟦[v,v,w]⟧`).  A `3`-edge must have
  three *distinct* vertices, so `Sym` would need a distinctness side condition carried everywhere,
  buying nothing.  `Finset` gives distinctness and unorderedness by construction, and it makes
  the counting bound `H ⊆ Finset.powersetCard 3 Finset.univ` a one-line `Finset.card_le_card`.
  ⛔ **Not the subtype `{e : Finset (Fin n) // #e = 3}`** either: that would push the uniformity
  proof into every edge term.
* **Vertices are `Fin n`.**  The labelling is irrelevant: `ex3` is a cardinality maximum and
  every relabelling is a bijection of `Fin n`.

## Conventions the source leaves unstated (each one NAMED, with the reading taken)

* **"a set of 4 vertices which is covered by all 4 possible $3$-edges" is a CONTAINMENT, not an
  induced copy.**  `ContainsK4 H` says: some `S` with `#S = 4` has *every* one of its four
  `3`-subsets in `H`.  `H` may contain arbitrarily many other edges, and edges meeting `S` in one
  or two vertices are unconstrained.  ⛔ This is the trap `SimpleGraph.Embedding` sets for the
  graph case: it is a `RelEmbedding`, i.e. an **iff** on adjacency, hence an *induced* copy.  A
  biconditional here would formalise a different — and much larger — extremal number.
* **"the largest number of 3-edges" counts EDGES, not incidences**, so it is `#H`.
* **"largest" is `sSup` over the achievable edge counts**, not a `max` over hypergraphs: a
  different `H` may witness each count.  The set is nonempty (`exSet_nonempty`, PROVED: `∅` is
  admissible) and bounded above by `n.choose 3` (`exSet_bddAbove`, PROVED), so the supremum is
  attained and agrees with "largest".
* **`n` is a natural number**, and `ex3 n` is a natural number.
* **The ratio $\mathrm{ex}_3(n,K_4^3)/\binom n3$ is a real division**, `density n`.  For `n < 3`
  the denominator is `0` and Lean's `/` yields `0` — a junk value, harmless only because every
  asymptotic statement is taken along `atTop`.  Named rather than hidden.
* **"the value of $\mathrm{ex}_3$" is read as the limit of the density.**  The source asks for a
  function of `n`; the resolution node answers with bounds of the form `c·binom n 3`, which fixes
  the intended normalisation.  This is the same reading the sibling entry [712] takes, where the
  resolution node calls it "this limit" explicitly.
* **`o(1)` and the upper bound are unfolded with an explicit `ε`** along `Filter.atTop`, rather
  than via `Asymptotics.IsLittleO`, so the statements are readable without unfolding filter
  machinery.  For the lower bound, `(5/9 + o(1))·binom n 3 ≤ ex3 n` is read as: for every `ε > 0`,
  eventually `(5/9 - ε)·binom n 3 ≤ ex3 n`.
* **"three equal parts $X_1,X_2,X_3$" is formalized as the residue partition `v ↦ v % 3`.**  When
  `3 ∤ n` the parts are only near-equal (sizes differ by at most one); no partition into exactly
  equal parts exists then, so "equal" cannot be taken literally, and the asymptotic density is
  unaffected.  ⛔ The choice of *which* balanced partition is irrelevant up to a bijection of
  `Fin n`, but a *specific* one had to be chosen to make `turanEdges` a definition rather than an
  existential.
* **"$X_{i+1}$ (where $X_4=X_1$)" is cyclic succession**, formalized as `j + 1` in `Fin 3`, which
  wraps.  The construction is *not* symmetric under swapping the two roles: two vertices in `X_i`
  plus one in `X_{i+1}` is an edge, two in `X_i` plus one in `X_{i-1}` is not.  The source's
  indexing is followed exactly.

## Degenerate instances — CHECKED BEFORE COMMITTING, each with its actual value

The live danger, inherited from the sibling #712 analysis, is that `IsCompleteOn` is a `∀` over
`3`-subsets of `S` with no nonemptiness guard, so it could go vacuously true and make "contains
`K_4^3`" hold of the empty hypergraph.  Here `3 ≤ 4` is a numeral fact, so that cannot happen —
but the boundary values were computed rather than assumed:

| `n` | `ex3 n` | why |
|---|---|---|
| `0` | `0` | no `3`-subsets of `Fin 0` exist, so the only 3-uniform `H` is `∅`; `choose 0 3 = 0` too |
| `1` | `0` | same; `choose 1 3 = 0` |
| `2` | `0` | same; `choose 2 3 = 0` |
| `3` | `1` | one `3`-edge exists and **no `4`-set exists**, so `{univ}` is `K_4^3`-free |

All four are the single PROVED statement `ex3_eq_choose_of_lt_four`: for `n < 4` there is no
`4`-element subset of `Fin n` at all, so *every* 3-uniform hypergraph is `K_4^3`-free and the
complete one is admissible.  ⛔ Note what this says about the source's displayed upper bound: at
`n = 3` the density is `1`, so `0.5611666` cannot hold for all `n` (see above).

`density n` at `n = 0,1,2` is `0/0 = 0`; at `n = 3` it is `1/1 = 1`.  Neither is a counterexample
to anything stated here, because every asymptotic statement is guarded by `∀ᶠ n in atTop`.

## The junk-value trap, closed

`ex3 n = sSup (exSet n)` and `Nat.sSup` returns `0` on a set that is empty **or** unbounded above.

* **Empty:** ruled out by `exSet_nonempty` (PROVED) — `∅` is 3-uniform and `K_4^3`-free, because
  a `4`-set has a `3`-subset (`Finset.exists_subset_card_eq`) and that subset is not in `∅`.
* **Unbounded:** ruled out by `exSet_bddAbove` (PROVED) — every admissible `H` sits inside
  `Finset.powersetCard 3 Finset.univ`, of card `n.choose 3`.

So `ex3_le_choose` is a genuine bound on a genuine maximum, and `ex3 0 = 0` is a real zero.

## Mathlib gaps (checked on the built Mathlib on this machine, `v4.31.0-rc1`)

`Mathlib/Combinatorics/` contains `SimpleGraph/`, `SetFamily/`, `Colex`, `Matroid/`, `Young/`,
`Enumerative/` — and **nothing `r`-uniform for `r > 2`**.  `SimpleGraph.extremalNumber`,
`SimpleGraph.IsContained`, `SimpleGraph.Copy`, `SimpleGraph.Free`, `SimpleGraph.turanDensity`
and `SimpleGraph.tendsto_turanDensity`
(`Mathlib/Combinatorics/SimpleGraph/Extremal/TuranDensity.lean`) are the `r = 2` case only, and
they do not generalise: they are stated for `SimpleGraph`, whose edge type is `Sym2`.  There is
no hypergraph type, no `r`-uniform extremal number, and no Turán density for `r > 2`.  Every
definition below is therefore written from scratch and none of it can be obtained by
instantiating Mathlib.  **Recorded as a Mathlib gap.**

## Relation to the sibling artifact `erdos-712.lean`

#712 is the general `k > r > 2` problem and its file defines `Erdos712.ex r k n` together with
`Erdos712.Erdos500Instance c := QuestionAt 3 4 c`.  This file is deliberately **standalone** —
it must elaborate on its own, and the two files are not part of one Lean library — so it
re-derives the `r = 3`, `k = 4` specialisations under its own names, in the same shapes, so the
two can be checked against each other by unfolding.  What is *new* here and absent there (by
#712's own explicit note) is Turán's `5/9` construction and Razborov's bound.

## Mathlib used

`Finset.powersetCard` / `Finset.mem_powersetCard` / `Finset.card_powersetCard`,
`Finset.exists_subset_card_eq`, `Finset.card_le_card`, `Finset.subset_univ`, `Finset.filter`,
`Nat.choose`, `sSup` / `le_csSup` / `csSup_le` on `ℕ` (`Mathlib.Data.Nat.Lattice`),
`Filter.atTop`, `Filter.Eventually`, `Filter.Tendsto`, `nhds` on `ℝ`, `tendsto_nhds_unique`.
-/

-- @category research open
-- @AMS 5
-- Category vocabulary and AMS tagging adopted from the formal-conjectures corpus
-- (509 files, measured 2026-08-28). Written as a comment rather than the corpus
-- attribute form, so this artifact still elaborates standalone, outside their project.








import Mathlib
namespace Erdos500

open Filter Topology

/-! ### The 3-uniform hypergraph, and what "covered by all 4 possible 3-edges" means -/

/-- `Is3Uniform H` : every edge of `H` has exactly three vertices.

A 3-uniform hypergraph on `n` vertices is an `H : Finset (Finset (Fin n))` satisfying this. -/
def Is3Uniform {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ H, e.card = 3

/-- `IsCompleteOn H S` : every `3`-subset of `S` is an edge of `H`.

With `#S = 4` this is the source's *"a set of 4 vertices which is covered by all 4 possible
3-edges"*.

⛔ One-directional on purpose: `H` may contain any other edges whatsoever.  A biconditional would
formalise an INDUCED copy — the `SimpleGraph.Embedding`/`RelEmbedding` trap — which is a different
problem. -/
def IsCompleteOn {n : ℕ} (H : Finset (Finset (Fin n))) (S : Finset (Fin n)) : Prop :=
  ∀ e ⊆ S, e.card = 3 → e ∈ H

/-- `ContainsK4 H` : `H` contains a `K_4^3` — four vertices all four of whose `3`-subsets are
edges. -/
def ContainsK4 {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∃ S : Finset (Fin n), S.card = 4 ∧ IsCompleteOn H S

/-- `IsK4Free H` : `H` contains no `K_4^3`. -/
def IsK4Free {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ¬ ContainsK4 H

/-- `Admissible H` : the two conditions the source imposes on the hypergraphs maximised over —
3-uniform, and `K_4^3`-free. -/
def Admissible {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  Is3Uniform H ∧ IsK4Free H

/-- The set of edge counts achievable by an admissible hypergraph on `n` vertices. -/
def exSet (n : ℕ) : Set ℕ :=
  {m | ∃ H : Finset (Finset (Fin n)), Admissible H ∧ H.card = m}

/-- `ex3 n` = $\mathrm{ex}_3(n,K_4^3)$ — *the largest number of `3`-edges which can be placed on
`n` vertices so that there exists no `K_4^3`*.

⛔ `sSup` on `ℕ` returns the junk value `0` on an empty or unbounded-above set.  Neither occurs:
`exSet_nonempty` and `exSet_bddAbove`, both PROVED below. -/
noncomputable def ex3 (n : ℕ) : ℕ := sSup (exSet n)

/-! ### Well-definedness and anti-vacuity — ALL PROVED (no `sorry`) -/

/-- Every admissible hypergraph lives inside the `3`-subsets of the vertex set. -/
theorem subset_powersetCard {n : ℕ} {H : Finset (Finset (Fin n))} (hH : Admissible H) :
    H ⊆ Finset.powersetCard 3 (Finset.univ : Finset (Fin n)) := by
  intro e he
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, hH.1 e he⟩

/-- **PROVED.** `exSet n` is bounded above by `n.choose 3`, so `ex3` is never `sSup`'s
unbounded-set junk value. -/
theorem exSet_bddAbove (n : ℕ) : BddAbove (exSet n) := by
  refine ⟨n.choose 3, ?_⟩
  rintro m ⟨H, hH, rfl⟩
  have h := Finset.card_le_card (subset_powersetCard hH)
  rwa [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h

/-- **PROVED.** The empty hypergraph is admissible, so `exSet n` is nonempty and `ex3 n = 0`
would be a real zero rather than `Nat.sSup`'s junk value.

⛔ This is where a `k < r` degeneracy would bite in the general problem: if a `4`-set had no
`3`-subsets, `IsCompleteOn` would be vacuously true and `∅` would CONTAIN `K_4^3`.  Here `3 ≤ 4`
is a numeral fact and `Finset.exists_subset_card_eq` supplies the refuting `3`-subset. -/
theorem exSet_nonempty (n : ℕ) : (exSet n).Nonempty := by
  refine ⟨0, (∅ : Finset (Finset (Fin n))), ⟨?_, ?_⟩, Finset.card_empty⟩
  · intro e he
    exact absurd he (Finset.notMem_empty e)
  · rintro ⟨S, hS, hcomp⟩
    obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (s := S) (n := 3) (by omega)
    exact Finset.notMem_empty t (hcomp t hts htcard)

/-- **PROVED — the counting control.**  `ex_3(n,K_4^3) ≤ \binom n3`: there are only `n.choose 3`
possible `3`-edges in the first place. -/
theorem ex3_le_choose (n : ℕ) : ex3 n ≤ n.choose 3 := by
  refine csSup_le (exSet_nonempty n) ?_
  rintro m ⟨H, hH, rfl⟩
  have hle := Finset.card_le_card (subset_powersetCard hH)
  rwa [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at hle

/-- **PROVED degenerate values, `n < 4`.**  With fewer than four vertices no `4`-set exists at
all, every 3-uniform hypergraph is `K_4^3`-free, and the complete 3-uniform hypergraph is
admissible: `ex3 n = n.choose 3`.

This settles all four boundary cases at once: `ex3 0 = ex3 1 = ex3 2 = 0` and `ex3 3 = 1`.
⛔ It is also the proof that the source's `0.5611666\binom n3` cannot be read as a `∀ n`
statement: at `n = 3` the ratio is `1`. -/
theorem ex3_eq_choose_of_lt_four {n : ℕ} (hn : n < 4) : ex3 n = n.choose 3 := by
  refine le_antisymm (ex3_le_choose n) ?_
  have hadm : Admissible (Finset.powersetCard 3 (Finset.univ : Finset (Fin n))) := by
    refine ⟨fun e he => (Finset.mem_powersetCard.mp he).2, ?_⟩
    rintro ⟨S, hS, -⟩
    have hcard : S.card ≤ n := by
      have := Finset.card_le_card (Finset.subset_univ S)
      rwa [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hmem : n.choose 3 ∈ exSet n := by
    refine ⟨Finset.powersetCard 3 (Finset.univ : Finset (Fin n)), hadm, ?_⟩
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact le_csSup (exSet_bddAbove n) hmem

/-- **PROVED small case.**  `ex3 0 = 0` — a real zero: `exSet 0 = {0}`, not the empty set. -/
theorem ex3_zero : ex3 0 = 0 := by
  rw [ex3_eq_choose_of_lt_four (by norm_num)]
  decide

/-- **PROVED small case.**  `ex3 2 = 0`: `Fin 2` has no `3`-subsets. -/
theorem ex3_two : ex3 2 = 0 := by
  rw [ex3_eq_choose_of_lt_four (by norm_num)]
  decide

/-- **PROVED computed case, the first nonzero value.**  `ex3 3 = 1`: the single `3`-edge on three
vertices is `K_4^3`-free because there is no `4`-set to be complete on. -/
theorem ex3_three : ex3 3 = 1 := by
  rw [ex3_eq_choose_of_lt_four (by norm_num)]
  decide

/-! ### The density, and THE QUESTION.  Open; no value is named. -/

/-- The normalised extremal number $\dfrac{\mathrm{ex}_3(n,K_4^3)}{\binom n3}$.

⛔ For `n < 3` the denominator is `0` and Lean's `/` yields `0`.  That junk value is harmless only
because every statement below is taken along `atTop`.  At `n = 3` the density is `1`. -/
noncomputable def density (n : ℕ) : ℝ := (ex3 n : ℝ) / (n.choose 3 : ℝ)

/-- The shape a resolution of #500 would take: *the density tends to `c`.*

Parametric in `c` on purpose.  ⛔ **No `c` is supplied to this anywhere in this file except inside
`TuranConjecture`, which is explicitly a conjecture, and inside the two bounds the source records
as known — neither of which names the value.** -/
def IsTuranDensity (c : ℝ) : Prop :=
  Tendsto (fun n : ℕ => density n) atTop (𝓝 c)

/-- **Erdős #500 (OPEN, $500).**  *"What is $\mathrm{ex}_3(n,K_4^3)$?"*

Formalised as: the normalised extremal number converges to some real number.

A `def`, not a `theorem`: the problem is open and this file takes no position on the value.  The
existential over `c` is what keeps the answer UNNAMED.  ⛔ See the header for the honest gap —
"what is the value" is strictly stronger than "a value exists", and here that gap is real, since
existence of the limit is classical while the value is the open problem. -/
def Question : Prop :=
  ∃ c : ℝ, IsTuranDensity c

/-- **PROVED.**  The density has at most one limit, so "the value of $\mathrm{ex}_3$" is well
posed and `Question`'s unnamed `c` is unambiguous.  Exercises `IsTuranDensity` against Mathlib's
uniqueness of limits in the Hausdorff space `ℝ`. -/
theorem turanDensity_unique {c c' : ℝ} (h : IsTuranDensity c) (h' : IsTuranDensity c') :
    c = c' :=
  tendsto_nhds_unique h h'

/-- **Turán's conjectured value (OPEN).**  The source: *"This is probably the truth."*

A belief recorded by the source, hence a `def : Prop` — never a theorem, and never `Question`'s
answer. -/
def TuranConjecture : Prop :=
  IsTuranDensity (5 / 9)

/-- **PROVED.**  If Turán's conjecture holds then the limit exists, i.e. `Question` holds.  Pure
bookkeeping over this file's own definitions, recorded so that the conjecture and the question
are not read as independent — and so that `TuranConjecture` is visibly a *strengthening*, not a
restatement. -/
theorem turanConjecture_imp_question (h : TuranConjecture) : Question :=
  ⟨5 / 9, h⟩

/-! ### Turán's explicit construction, spelled out as the source spells it out -/

/-- The part of `Fin n` a vertex belongs to: `X_0, X_1, X_2` are the residue classes mod `3`.

The source says "three equal parts"; when `3 ∤ n` no exactly-equal partition exists, and this one
is balanced to within a single vertex, which is what the asymptotic statement needs. -/
def partOf {n : ℕ} (v : Fin n) : Fin 3 :=
  ⟨(v : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- How many vertices of the edge `e` lie in part `j`. -/
def partCard {n : ℕ} (e : Finset (Fin n)) (j : Fin 3) : ℕ :=
  (e.filter (fun v => partOf v = j)).card

/-- The source's edge rule: *"those triples that either have exactly one vertex in each part or
two vertices in $X_i$ and one vertex in $X_{i+1}$ (where $X_4=X_1$)"*.

⛔ `j + 1` is addition in `Fin 3`, so it wraps — that is the source's `X_4 = X_1`.  The rule is
asymmetric: two in `X_i` and one in `X_{i-1}` is NOT an edge. -/
def TuranAdmissible {n : ℕ} (e : Finset (Fin n)) : Prop :=
  (∀ j : Fin 3, partCard e j = 1) ∨ (∃ j : Fin 3, partCard e j = 2 ∧ partCard e (j + 1) = 1)

instance decTuranAdmissible {n : ℕ} (e : Finset (Fin n)) : Decidable (TuranAdmissible e) := by
  unfold TuranAdmissible
  infer_instance

/-- Turán's construction: all `3`-subsets of `Fin n` obeying the rule above. -/
def turanEdges (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.powersetCard 3 (Finset.univ : Finset (Fin n))).filter TuranAdmissible

/-- **PROVED.**  Turán's construction is 3-uniform — it is carved out of `powersetCard 3`.
An anti-vacuity control on `turanEdges`: whatever the edge rule does, the result really is a
3-uniform hypergraph. -/
theorem turanEdges_is3Uniform (n : ℕ) : Is3Uniform (turanEdges n) := by
  intro e he
  rw [turanEdges, Finset.mem_filter] at he
  exact (Finset.mem_powersetCard.mp he.1).2

/-- **PROVED.**  Turán's construction is one of the hypergraphs `ex3` maximises over, *given* that
it is `K_4^3`-free (the content, stated separately as `turan_construction_free`).  Recorded as an
implication so that the lower bound below is visibly a consequence of the construction and not an
independent assertion. -/
theorem turanEdges_card_le_ex3_of_free (n : ℕ) (hfree : IsK4Free (turanEdges n)) :
    (turanEdges n).card ≤ ex3 n :=
  le_csSup (exSet_bddAbove n) ⟨turanEdges n, ⟨turanEdges_is3Uniform n, hfree⟩, rfl⟩

/-! ### What the resolution node records as KNOWN.  Stated with `sorry`, not proved here. -/

/-- **Turán's construction is `K_4^3`-free.**  This is the combinatorial content of the source's
*"Tur\'{a}n observed that dividing the vertices into three equal parts ... shows that ..."*. -/
theorem turan_construction_free (n : ℕ) : IsK4Free (turanEdges n) := by
  sorry

/-- **Turán's construction has density `5/9 + o(1)`.**  The counting half of the same
observation: the triples with one vertex in each part contribute `≈ (n/3)^3 = n^3/27`, and for
each of the three cyclic pairs `(X_i, X_{i+1})` the triples with two vertices in `X_i` and one in
`X_{i+1}` contribute `≈ binom (n/3) 2 · (n/3) ≈ n^3/54`, giving
`n^3/27 + 3·n^3/54 = 5n^3/54 = (5/9)·binom n 3 + o(n^3)`. -/
theorem turan_construction_card (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((5 : ℝ) / 9 - ε) * (n.choose 3 : ℝ) ≤ ((turanEdges n).card : ℝ) := by
  sorry

/-- **The lower bound the source records (Turán).**
\[\mathrm{ex}_3(n,K_4^3)\geq\left(\frac{5}{9}+o(1)\right)\binom{n}{3}.\]

The `o(1)` is unfolded with an explicit `ε` along `atTop`.  ⛔ This is a bound, not the value:
nothing here says the `5/9` is tight. -/
theorem turan_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((5 : ℝ) / 9 - ε) * (n.choose 3 : ℝ) ≤ (ex3 n : ℝ) := by
  sorry

/-- **The upper bound the source records (Razborov, `Ra10`).**
\[\mathrm{ex}_3(n,K_4^3)\leq 0.5611666\binom{n}{3}.\]

⛔ Stated with an `ε` along `atTop`, NOT as `∀ n`: the literal `∀ n` reading is false at `n = 3`,
where `ex3_three` gives density `1`.  See the header. -/
theorem razborov_upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (ex3 n : ℝ) ≤ (0.5611666 + ε) * (n.choose 3 : ℝ) := by
  sorry

/-- **Turán's bound, phrased on the limiting density.**  Any limit of the density is at least
`5/9`.

⛔ CONDITIONAL: vacuous if no limit exists.  Existence is classical but is not recorded by this
source, so it is not stated here (see the header).  The unconditional content is
`turan_lower_bound`. -/
theorem turan_density_lower (c : ℝ) (hc : IsTuranDensity c) : (5 : ℝ) / 9 ≤ c := by
  sorry

/-- **Razborov's bound, phrased on the limiting density.**  Any limit of the density is at most
`0.5611666`.

⛔ CONDITIONAL, exactly as above.  Together with `turan_density_lower` this confines the unnamed
`c` of `Question` to `[5/9, 0.5611666]` — and confining it is precisely NOT determining it, which
is why #500 is open. -/
theorem razborov_density_upper (c : ℝ) (hc : IsTuranDensity c) : c ≤ 0.5611666 := by
  sorry

/-- Recorded so the interval is visible in one place: `5/9 = 0.555… < 0.5611666`, so the two
bounds are consistent and leave a genuine gap.  ⛔ A `theorem` about numerals only — it says
nothing about `ex3`. -/
theorem turan_lt_razborov : (5 : ℝ) / 9 < 0.5611666 := by
  norm_num

end Erdos500

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos500.subset_powersetCard
#print axioms Erdos500.exSet_bddAbove
#print axioms Erdos500.exSet_nonempty
#print axioms Erdos500.ex3_le_choose
#print axioms Erdos500.ex3_eq_choose_of_lt_four
#print axioms Erdos500.ex3_zero
#print axioms Erdos500.ex3_two
#print axioms Erdos500.ex3_three
#print axioms Erdos500.turanDensity_unique
#print axioms Erdos500.turanConjecture_imp_question
#print axioms Erdos500.turanEdges_is3Uniform
#print axioms Erdos500.turanEdges_card_le_ex3_of_free
#print axioms Erdos500.turan_construction_free
#print axioms Erdos500.turan_construction_card
#print axioms Erdos500.turan_lower_bound
#print axioms Erdos500.razborov_upper_bound
#print axioms Erdos500.turan_density_lower
#print axioms Erdos500.razborov_density_upper
#print axioms Erdos500.turan_lt_razborov
