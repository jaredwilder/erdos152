/-
# Erdős problem #712 — the general Turán hypergraph density  (**OPEN**, $500 prize)

## The question (verbatim from the frozen source, node `n000-question`)

> Determine, for any $k>r>2$, the value of
> \[\frac{\mathrm{ex}_r(n,K_k^r)}{\binom{n}{r}},\]
> where $\mathrm{ex}_r(n,K_k^r)$ is the largest number of $r$-edges which can placed on $n$
> vertices so that there exists no set of $k$ vertices which is covered by all $\binom{k}{r}$
> possible $r$-edges.

## The resolution node (verbatim, node `n001-resolution`)

> Tur\'{a}n proved that, when $r=2$, this limit is
> \[\frac{1}{2}\left(1-\frac{1}{k-1}\right).\]
> Erd\H{o}s \cite{Er81} offered \$500 for the determination of this value for any fixed
> $k>r>2$, and \$1000 for 'clearing up the whole set of problems'.
> See also [500] for the case $r=3$ and $k=4$.

## What is formalized here — and what is deliberately NOT

**This problem is OPEN.**  This file states the QUESTION and asserts no answer to it.
`Erdos712.Question` and `Erdos712.QuestionAt` are `def ... : Prop`, never theorems, and neither
names a value for the limit.  There is no `erdos_712_resolution`, and nowhere in this file does
any real number appear as *the* density for a `k > r > 2`.

The ONE item the resolution node records as established is Turán's `r = 2` value.  It appears as
`turan_density_two` — a `theorem` with `sorry`, named after the author the source credits.

⛔ **The `5/9` construction and Razborov's `0.5611666` upper bound are NOT in this file.**  They
belong to the sibling entry [500] (`r = 3`, `k = 4`), and #712's own resolution node does not
state them.  Importing them here would be citing a source this artifact was not given.

⛔ **No sorried theorem asserts that the limit exists.**  Writing the ratio's "value" presupposes
convergence, and in the literature that presupposition is discharged by an averaging argument,
not by the open problem.  But #712's resolution node never states such a lemma, so — following
the same discipline that kept Rankin's unstated bound out of the sibling #687 file — it is named
here in prose and asserted nowhere in code.

## The gap between `Question` and the prize, named honestly

`Question` says: *for every `k > r > 2` the ratio converges to some real number.*  That is
strictly weaker than what Erdős paid $500 for, which is *determining* that number as a function
of `k` and `r`.  No `Prop` can demand a determination: "compute this" is not a proposition.
Formal-conjectures handles such entries with their `answer(sorry)` idiom, which does not
elaborate outside their project, so it is not used here.  `Question` is therefore the strongest
statement about #712 that can be made **without naming an answer**, and this paragraph is the
record that it is weaker than the problem.  `QuestionAt r k c` is supplied as the shape a future
resolution would take — it is parametric in `c`, and no `c` is ever supplied.

## Conventions the source leaves unstated (each one NAMED, with the reading taken)

* **"covered by all $\binom{k}{r}$ possible $r$-edges" = the COMPLETE `r`-uniform hypergraph on
  those `k` vertices.**  `S` with `#S = k` is such a set exactly when *every* `r`-element subset
  of `S` is an edge of `H`.  This is `IsCompleteOn` below.  ⛔ It is a *containment*, not an
  induced-subgraph condition: `H` may have any number of other edges, and edges meeting `S`
  partially are unconstrained.  (The sibling note about `SimpleGraph.Embedding` being a
  `RelEmbedding`, hence an IFF on adjacency and therefore an INDUCED copy, is exactly the trap
  avoided by spelling the condition out as a one-directional `∀ e ⊆ S, #e = r → e ∈ H`.)
* **An `r`-uniform hypergraph on `n` vertices** is `H : Finset (Finset (Fin n))` together with
  `∀ e ∈ H, #e = r`.  Vertices are `Fin n`; the labelling is irrelevant because `ex` is a
  cardinality maximum and every relabelling is a bijection of `Fin n`.  ⛔ No subtype
  `{e // #e = r}` is used: it would force the uniformity proof into every edge term and make the
  `H ⊆ powersetCard r univ` bound harder to state, not easier.
* **`ex_r(n, K_k^r)` is a supremum over admissible hypergraphs**, `sSup` on `ℕ` of the set of
  achievable edge counts.  `Nat.sSup` returns the junk value `0` on a set that is empty or
  unbounded above; both halves are closed here and PROVED (see the junk-value section).
* **"largest number of `r`-edges which can be placed" counts EDGES, not incidences**, so it is
  `#H`, and it is compared against `n.choose r`, the total number of `r`-edges available.
* **`r`, `k`, `n` are natural numbers.**  The source's `k > r > 2` is `2 < r` and `r < k`.
* **The ratio is a real division.**  `density r k n = (ex r k n : ℝ) / (n.choose r : ℝ)`.  For
  `n < r` the denominator is `0` and Lean's division gives `0`; that is a junk value, and it is
  harmless only because every asymptotic statement is taken along `Filter.atTop`, where
  eventually `n ≥ r`.  Named rather than hidden.
* **"the value of the ratio" is read as a LIMIT as `n → ∞`**, `Tendsto (density r k) atTop
  (𝓝 c)`.  The source writes a ratio depending on `n` and asks for "the value", which only makes
  sense as an asymptotic quantity; the resolution node confirms the reading by calling it
  "this limit".

## Degenerate instances — CHECKED BEFORE COMMITTING, each with its actual value

The live danger in this definition is that `IsCompleteOn` is a `∀` over `r`-subsets of `S` with
no nonemptiness guard, so it can go **vacuously true** and make "contains `K_k^r`" hold of the
empty hypergraph.  All four boundary cases were computed rather than assumed:

| instance | what happens | handled by |
|---|---|---|
| `k < r` | `S` with `#S = k` has NO `r`-subsets, so `IsCompleteOn` is vacuously true and *every* `H` — including `∅` — contains `K_k^r`.  `exSet` is EMPTY and `ex` is `Nat.sSup`'s junk `0`. | ⛔ **GUARDED.** Every statement about `ex` here carries `r ≤ k`; `Question` carries the source's own `2 < r`, `r < k`. |
| `r = k` | `S := e` for any edge `e` is complete-on, since `e` is its own only `r`-subset.  So an admissible `H` is empty and `ex r r n = 0`. | PROVED: `ex_self_eq_zero`. A real zero, not the junk one. |
| `n < k` | no `S` of card `k` exists at all, so every uniform `H` is free and the complete hypergraph is admissible: `ex r k n = n.choose r`, density `1`. | PROVED: `ex_eq_choose_of_card_lt`. |
| `n < r` | no `r`-subsets of `Fin n` exist, so the only uniform `H` is `∅`: `ex r k n = 0 = n.choose r`, and `density = 0/0 = 0`. | Subsumed by the previous row (`n < r ≤ k`); `Nat.choose_eq_zero_of_lt` makes both sides `0`. |

The `k < r` row is the one that matches the sibling failure this file was warned about, and it is
the reason `r ≤ k` is a hypothesis and not a comment.

## The junk-value trap, closed

`ex r k n = sSup (exSet r k n)` where `exSet` is the set of achievable edge counts.

* **Empty:** ruled out by `exSet_nonempty` (PROVED, needs `r ≤ k`): `∅` is admissible, because a
  `k`-set has an `r`-subset when `r ≤ k` and that subset is not in `∅`.
* **Unbounded:** ruled out by `exSet_bddAbove` (PROVED, unconditional): every admissible `H` sits
  inside `Finset.powersetCard r Finset.univ`, whose card is `n.choose r`.

Hence `ex_le_choose` — `ex r k n ≤ n.choose r`, the control this file was asked for — is a
genuine bound on a genuine maximum, and `density r k n ∈ [0,1]` for `n ≥ r`.

## Sibling status

`erdos-500.lean` (the `r = 3`, `k = 4` special case) was **NOT on disk** when this file was
written, so these definitions are this file's own.  `Erdos712.Erdos500Instance` is provided as
the exact instantiation `QuestionAt 3 4`, so that a later #500 artifact can be checked against
this one by unfolding rather than by reading.

## Mathlib gaps (checked, not guessed)

Searched the built Mathlib on this machine (`v4.31.0-rc1`).  **The string "hypergraph" does not
occur anywhere in Mathlib.**  `Mathlib/Combinatorics/` has `SimpleGraph/`, `SetFamily/`,
`Extremal/RuzsaSzemeredi.lean`, `Colex`, `Matroid`, `Young` — nothing `r`-uniform.
`SimpleGraph.extremalNumber`, `SimpleGraph.IsContained`, `SimpleGraph.Copy`,
`SimpleGraph.turanDensity`, `SimpleGraph.tendsto_turanDensity`
(`Mathlib/Combinatorics/SimpleGraph/Extremal/TuranDensity.lean`) are the `r = 2` case ONLY and do
not generalise: they are stated for `SimpleGraph`, whose edges are `Sym2`.  So every definition
below is written from scratch, and none of it can be obtained by instantiating Mathlib.

## Mathlib used

`Finset.powersetCard` / `Finset.mem_powersetCard` / `Finset.card_powersetCard`,
`Finset.exists_subset_card_eq`, `Finset.eq_of_subset_of_card_le`, `Finset.card_le_card`,
`Nat.choose`, `Nat.choose_eq_zero_of_lt`, `sSup` / `le_csSup` / `csSup_le` on `ℕ`
(`Mathlib.Data.Nat.Lattice`), `Filter.atTop`, `Filter.Tendsto`, `nhds` on `ℝ`.
-/

-- @category research open
-- @AMS 5
-- Category vocabulary and AMS tagging adopted from the formal-conjectures corpus
-- (509 files, measured 2026-08-28). Written as a comment rather than the corpus
-- attribute form, so this artifact still elaborates standalone, outside their project.








import Mathlib
namespace Erdos712

open Filter Topology

/-! ### The `r`-uniform hypergraph, and what "covered by all $\binom{k}{r}$ possible $r$-edges"
means -/

/-- `IsUniform r H` : every edge of `H` has exactly `r` vertices.

An `r`-uniform hypergraph on `n` vertices is a `H : Finset (Finset (Fin n))` satisfying this. -/
def IsUniform (r : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ H, e.card = r

/-- `IsCompleteOn r H S` : *`S` is a set of vertices covered by all possible `r`-edges*, i.e. the
complete `r`-uniform hypergraph `K^r` on `S` sits inside `H`.

This is the source's phrase "a set of $k$ vertices which is covered by all $\binom{k}{r}$
possible $r$-edges", with the `#S = k` part carried separately by `ContainsClique`.

⛔ One-directional on purpose: `H` may contain any other edges whatsoever.  A biconditional here
would formalise an INDUCED copy, which is a different (and false) problem. -/
def IsCompleteOn (r : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) (S : Finset (Fin n)) : Prop :=
  ∀ e ⊆ S, e.card = r → e ∈ H

/-- `ContainsClique r k H` : `H` contains `K_k^r` — some `k` vertices all of whose `r`-subsets
are edges. -/
def ContainsClique (r k : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∃ S : Finset (Fin n), S.card = k ∧ IsCompleteOn r H S

/-- `Admissible r k H` : `H` is `r`-uniform and `K_k^r`-free — the two conditions the source
imposes on the hypergraphs being maximised over. -/
def Admissible (r k : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  IsUniform r H ∧ ¬ ContainsClique r k H

/-- The set of edge counts achievable by an admissible hypergraph on `n` vertices. -/
def exSet (r k n : ℕ) : Set ℕ :=
  {m | ∃ H : Finset (Finset (Fin n)), Admissible r k H ∧ H.card = m}

/-- `ex r k n` = $\mathrm{ex}_r(n,K_k^r)$ — *the largest number of `r`-edges which can be placed
on `n` vertices so that there exists no set of `k` vertices covered by all possible `r`-edges.*

⛔ `sSup` on `ℕ` returns the junk value `0` on an empty or unbounded-above set.  Neither occurs
under `r ≤ k`: see `exSet_nonempty` and `exSet_bddAbove`, both PROVED below. -/
noncomputable def ex (r k n : ℕ) : ℕ := sSup (exSet r k n)

/-! ### Well-definedness and anti-vacuity — ALL PROVED (no `sorry`) -/

/-- Every admissible hypergraph lives inside the `r`-subsets of the vertex set. -/
theorem subset_powersetCard {r k n : ℕ} {H : Finset (Finset (Fin n))}
    (hH : Admissible r k H) : H ⊆ Finset.powersetCard r (Finset.univ : Finset (Fin n)) := by
  intro e he
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, hH.1 e he⟩

/-- **PROVED.** `exSet` is bounded above by `n.choose r`, so `ex` is never `sSup`'s
unbounded-set junk value. -/
theorem exSet_bddAbove (r k n : ℕ) : BddAbove (exSet r k n) := by
  refine ⟨n.choose r, ?_⟩
  rintro m ⟨H, hH, rfl⟩
  have h := Finset.card_le_card (subset_powersetCard hH)
  rwa [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h

/-- **PROVED, and the control this file was asked for:** `ex_r(n,K_k^r) ≤ \binom{n}{r}`.
There are only `n.choose r` possible `r`-edges in the first place. -/
theorem ex_le_choose (r k n : ℕ) : ex r k n ≤ n.choose r := by
  rcases Set.eq_empty_or_nonempty (exSet r k n) with h | h
  · simp [ex, h]
  · refine csSup_le h ?_
    rintro m ⟨H, hH, rfl⟩
    have hle := Finset.card_le_card (subset_powersetCard hH)
    rwa [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at hle

/-- **PROVED (needs `r ≤ k`).** The empty hypergraph is admissible, so `exSet` is nonempty.

⛔ This is precisely where the `k < r` degeneracy would bite: if `k < r`, a `k`-set has no
`r`-subsets, `IsCompleteOn` is vacuously true, and `∅` would CONTAIN `K_k^r`.  The hypothesis
`r ≤ k` is what supplies the `r`-subset that refutes containment. -/
theorem exSet_nonempty {r k : ℕ} (hrk : r ≤ k) (n : ℕ) : (exSet r k n).Nonempty := by
  refine ⟨0, (∅ : Finset (Finset (Fin n))), ⟨?_, ?_⟩, Finset.card_empty⟩
  · intro e he
    exact absurd he (Finset.notMem_empty e)
  · rintro ⟨S, hS, hcomp⟩
    obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (s := S) (n := r) (by omega)
    exact Finset.notMem_empty t (hcomp t hts htcard)

/-- **PROVED degenerate value, `r = k`.**  `ex r r n = 0`.

Any edge `e` is itself a `k = r` element set all of whose `r`-subsets (namely `e` alone) are
edges, so an admissible hypergraph has no edges at all.  This is a REAL zero, obtained as the
supremum of `{0}`, not `Nat.sSup`'s junk value — `exSet_nonempty` gives nonemptiness. -/
theorem ex_self_eq_zero (r n : ℕ) : ex r r n = 0 := by
  refine le_antisymm (csSup_le (exSet_nonempty (le_refl r) n) ?_) (Nat.zero_le _)
  rintro m ⟨H, hH, rfl⟩
  rw [Nat.le_zero, Finset.card_eq_zero]
  by_contra hne
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  refine hH.2 ⟨e, hH.1 e he, ?_⟩
  intro f hfe hfcard
  have : f = e := Finset.eq_of_subset_of_card_le hfe (by rw [hfcard, hH.1 e he])
  exact this ▸ he

/-- **PROVED degenerate value, `n < k`.**  When there are fewer than `k` vertices no `k`-set
exists, every uniform hypergraph is `K_k^r`-free, and the complete `r`-uniform hypergraph is
admissible: `ex r k n = n.choose r`, i.e. density `1`.

This also covers `n < r` (since `r ≤ k`), where both sides are `0` by
`Nat.choose_eq_zero_of_lt` — so `density` there is the harmless `0/0 = 0`. -/
theorem ex_eq_choose_of_card_lt {r k n : ℕ} (hnk : n < k) : ex r k n = n.choose r := by
  refine le_antisymm (ex_le_choose r k n) ?_
  have hadm : Admissible r k (Finset.powersetCard r (Finset.univ : Finset (Fin n))) := by
    refine ⟨fun e he => (Finset.mem_powersetCard.mp he).2, ?_⟩
    rintro ⟨S, hS, -⟩
    have : S.card ≤ n := by
      have := Finset.card_le_card (Finset.subset_univ S)
      rwa [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hmem : n.choose r ∈ exSet r k n := by
    refine ⟨Finset.powersetCard r (Finset.univ : Finset (Fin n)), hadm, ?_⟩
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact le_csSup (exSet_bddAbove r k n) hmem

/-! ### The ratio, and THE QUESTION.  Open; no value is named. -/

/-- The source's ratio $\dfrac{\mathrm{ex}_r(n,K_k^r)}{\binom{n}{r}}$.

⛔ For `n < r` the denominator is `0` and Lean's `/` yields `0`.  That junk value is harmless
only because every statement below is taken along `atTop`. -/
noncomputable def density (r k n : ℕ) : ℝ := (ex r k n : ℝ) / (n.choose r : ℝ)

/-- The shape a resolution of #712 would take: *the ratio tends to `c`.*

Parametric in `c` on purpose.  **No `c` is ever supplied anywhere in this file.** -/
def QuestionAt (r k : ℕ) (c : ℝ) : Prop :=
  Tendsto (fun n : ℕ => density r k n) atTop (𝓝 c)

/-- **Erdős #712 (OPEN, $500).**  *"Determine, for any $k>r>2$, the value of
$\frac{\mathrm{ex}_r(n,K_k^r)}{\binom{n}{r}}$."*

Formalised as: for every `k > r > 2` the ratio converges to some real number.

This is a `def`, not a `theorem`: the problem is open and this file takes no position on it, and
the existential over `c` is what keeps the value UNNAMED.  See the header for the honest gap —
"determine the value" is strictly stronger than "a value exists", and no `Prop` can demand a
determination. -/
def Question : Prop :=
  ∀ r k : ℕ, 2 < r → r < k → ∃ c : ℝ, QuestionAt r k c

/-- The `r = 3`, `k = 4` instance, which the source calls out as entry [500].

⛔ `erdos-500.lean` was not on disk when this file was written, so it reuses nothing; this
declaration exists so that a later #500 artifact can be checked against #712 by unfolding.
Still a `def`: [500] is open too, and no value is named here either. -/
def Erdos500Instance (c : ℝ) : Prop := QuestionAt 3 4 c

/-! ### What the resolution node records as KNOWN.  Stated with `sorry`, not proved here. -/

/-- **Turán's theorem, the `r = 2` case (`Tu41`, as recorded by the resolution node).**

> Tur\'{a}n proved that, when $r=2$, this limit is
> $\frac{1}{2}\left(1-\frac{1}{k-1}\right)$.

⛔ This is the `r = 2` boundary and is therefore OUTSIDE the source's range `k > r > 2`.  It is
recorded because the node records it, and because it is what fixes the intended reading of "the
value of the ratio" as a limit.  It answers nothing about #712.

`(k : ℝ) - 1` is real subtraction; `2 < k` keeps it positive. -/
theorem turan_density_two (k : ℕ) (hk : 2 < k) :
    QuestionAt 2 k ((1 : ℝ) / 2 * (1 - 1 / ((k : ℝ) - 1))) := by
  sorry

/-- Recorded so the two levels of the prize are not confused: Erdős offered \$500 for a single
fixed pair `k > r > 2`, and \$1000 for "clearing up the whole set of problems".  The uniform
statement is exactly `Question`; the per-pair statement is `∃ c, QuestionAt r k c`.

⛔ A `def`, not a theorem — this is bookkeeping about the open problem, not a claim about it. -/
def QuestionSinglePair (r k : ℕ) : Prop :=
  2 < r → r < k → ∃ c : ℝ, QuestionAt r k c

/-- The uniform \$1000 form implies every single-pair \$500 form.  PROVED (no `sorry`): it is
pure quantifier bookkeeping over this file's own definitions, and it is here so that the two
statements above are not read as independent. -/
theorem question_imp_singlePair (h : Question) (r k : ℕ) : QuestionSinglePair r k :=
  fun hr hrk => h r k hr hrk

end Erdos712

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos712.subset_powersetCard
#print axioms Erdos712.exSet_bddAbove
#print axioms Erdos712.ex_le_choose
#print axioms Erdos712.exSet_nonempty
#print axioms Erdos712.ex_self_eq_zero
#print axioms Erdos712.ex_eq_choose_of_card_lt
#print axioms Erdos712.turan_density_two
#print axioms Erdos712.question_imp_singlePair
