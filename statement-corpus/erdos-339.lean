/-
# Erdős problem 339 — affirmative resolution (Hegyvári, Hennecart, Plagne)

SOURCE (frozen, byte-exact, `erdos-339.tex`), quoted in full:

> Let $A\subseteq \mathbb{N}$ be a basis of order $r$. Must the set of integers representable
> as the sum of exactly $r$ distinct elements from $A$ have positive lower density?
> Erdős and Graham also ask whether if the set of integers which are the sum of $r$ elements
> from $A$ has positive upper density then must the set of integers representable as the sum
> of exactly $r$ distinct elements have positive upper density?
> The answer to both questions is yes, as proved by Hegyvári, Hennecart, and Plagne.

Both questions are formalized, as two separate theorems, neither merged into the other.

## Conventions the source leaves unstated (declared, not silently chosen)

1. **"basis of order r"**: taken as `∀ n : ℕ, n is a sum of exactly r elements of A, repetitions
   allowed`.  The source writes "basis", not "asymptotic basis", so the condition is imposed at
   *every* n rather than at all sufficiently large n.  Repetition is allowed here precisely
   because the *conclusion* is the one that insists on distinctness ("exactly r **distinct**
   elements"); if repetitions were already banned in the hypothesis the question would be empty.
2. **"sum of r elements from A"** (hypothesis of the second question): same reading — an r-tuple
   of elements of A, repetitions allowed.
3. **"sum of exactly r distinct elements"**: an r-element **Finset** contained in A.  `Finset.card
   = r` forces exactly r, and Finset-hood forces pairwise distinctness.  This is the load-bearing
   distinction from (1)/(2).
4. **ℕ contains 0** (Lean's ℕ).  Nothing in the source excludes it, and 0 ∈ A is harmless.
5. **density**: Mathlib has no natural/asymptotic density for subsets of ℕ (only Schnirelmann
   density, which is an infimum, not a liminf, and is therefore a *different* notion), so lower
   and upper density are defined here as `liminf`/`limsup` of |S ∩ [0,n)| / n along `atTop` — the
   standard asymptotic lower/upper density.  Counting on [0,n) versus [1,n] does not change either
   value.  No hypothesis of the source is dropped and none is added.
6. **r = 0** is not excluded, because the source does not exclude it; for r = 0 the basis
   hypothesis is simply unsatisfiable, so no extra assumption is needed.

## The `liminf`/`limsup` junk region, and why it cannot fire here (PROVED below)

`Filter.liminf f l` is `sSup {a | ∀ᶠ x in l, a ≤ f x}` and `Filter.limsup f l` is
`sInf {a | ∀ᶠ x in l, f x ≤ a}`, taken in the CONDITIONALLY complete lattice `ℝ`. Neither `sSup`
nor `sInf` is total there: on an empty set, or on a set unbounded on the relevant side, Mathlib
returns the junk value `0`, silently and with no error. That is a live hazard for this file: both
`erdos_339_lower` and `erdos_339_upper` are statements of the form `0 < density …`, and a
quantity whose true `liminf` were `+∞` would print as `0` — INVERTING the truth value. It is also
a hazard in the HYPOTHESIS of `erdos_339_upper`, where a junk `0` would make the assumption
unsatisfiable and the theorem vacuous.

⛔ Here the junk region is UNREACHABLE, and that is proved rather than asserted. `countingRatio
S n` lies in `[0,1]` for every `S` and every `n` (`countingRatio_nonneg`, `countingRatio_le_one`;
the degenerate `n = 0` case is `0/0 = 0`, which is in range, so it needs no exclusion). Hence the
two sets whose `sSup`/`sInf` define `lowerDensity`/`upperDensity` are NONEMPTY and BOUNDED on the
side that matters: `liminfSet_nonempty`, `liminfSet_bddAbove`, `limsupSet_nonempty`,
`limsupSet_bddBelow`, all `sorry`-free below, with `lowerDensity_eq_sSup` /
`upperDensity_eq_sInf` pinning that those are the very sets Mathlib takes the `sSup`/`sInf` of.
So both densities are genuine suprema/infima of nonempty bounded sets and no junk value can be
returned. No theorem in this file is restated or weakened by this; the facts are added.

Compare the sibling `erdos-1191.lean`, where the analogous weight is NOT known to be bounded
above and the trap is therefore closed the other way — by a junk-free restatement of the
question, with no equivalence asserted. Here a bound exists, so the stronger closure is used.
The sibling `erdos-449.lean` carries the identical `countingRatio` and the identical closure.
-/

-- @category research solved
-- @AMS 11
-- Category vocabulary and AMS tagging adopted from the
-- formal-conjectures corpus (509 files, measured 2026-08-28). Written as a comment
-- rather than the corpus attribute form, so this artifact still elaborates
-- standalone, outside their project.









import Mathlib
open Filter Finset

namespace Erdos339

/-- `|S ∩ [0, n)| / n`, the counting ratio whose `liminf`/`limsup` are the asymptotic
lower/upper densities of `S ⊆ ℕ`. -/
noncomputable def countingRatio (S : Set ℕ) (n : ℕ) : ℝ :=
  ((S ∩ Set.Iio n).ncard : ℝ) / (n : ℝ)

/-- Asymptotic **lower** density of a set of naturals. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ := liminf (countingRatio S) atTop

/-- Asymptotic **upper** density of a set of naturals. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ := limsup (countingRatio S) atTop

/-- `A` is a basis of order `r`: every natural number is a sum of exactly `r` elements of `A`,
repetitions allowed. -/
def IsBasisOfOrder (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ n : ℕ, ∃ f : Fin r → ℕ, (∀ i, f i ∈ A) ∧ ∑ i, f i = n

/-- The integers which are the sum of `r` elements of `A`, **repetitions allowed**. -/
def sumsOfExactly (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {n | ∃ f : Fin r → ℕ, (∀ i, f i ∈ A) ∧ ∑ i, f i = n}

/-- The integers representable as the sum of exactly `r` **distinct** elements of `A`. -/
def sumsOfDistinct (A : Set ℕ) (r : ℕ) : Set ℕ :=
  {n | ∃ F : Finset ℕ, ↑F ⊆ A ∧ F.card = r ∧ ∑ x ∈ F, x = n}

/-- **First question, answered yes.** If `A ⊆ ℕ` is a basis of order `r`, then the set of integers
representable as the sum of exactly `r` distinct elements of `A` has positive lower density. -/
theorem erdos_339_lower (A : Set ℕ) (r : ℕ) (hA : IsBasisOfOrder A r) :
    0 < lowerDensity (sumsOfDistinct A r) := by
  sorry

/-- **Second question, answered yes.** If the set of integers which are the sum of `r` elements of
`A` (repetitions allowed) has positive upper density, then the set of integers representable as the
sum of exactly `r` distinct elements of `A` has positive upper density. -/
theorem erdos_339_upper (A : Set ℕ) (r : ℕ)
    (h : 0 < upperDensity (sumsOfExactly A r)) :
    0 < upperDensity (sumsOfDistinct A r) := by
  sorry

/-! ### Anti-vacuity controls (PROVED, not part of the source)

A `sorry`-carrying statement elaborates whether or not its definitions say anything. The
lemmas below are fully proved and mention only this file's own definitions, so they are cheap
machine-checked evidence that those definitions bite. -/

/-- **The load-bearing check on conventions 2 and 3.** A sum of exactly `r` *distinct*
elements of `A` is in particular a sum of `r` elements of `A` with repetitions allowed:
enumerating an `r`-element `Finset` gives an `r`-tuple. If this failed, the two notions the
source contrasts would not be nested the way the source's wording ("sum of `r` elements"
versus "sum of exactly `r` **distinct** elements") requires, and the second theorem's
hypothesis would not be the weaker of the two. -/
-- @category test
theorem sumsOfDistinct_subset_sumsOfExactly (A : Set ℕ) (r : ℕ) :
    sumsOfDistinct A r ⊆ sumsOfExactly A r := by
  rintro n ⟨F, hFA, hcard, hsum⟩
  obtain ⟨e⟩ : Nonempty (Fin r ≃ {x // x ∈ F}) :=
    ⟨(finCongr hcard.symm).trans F.equivFin.symm⟩
  refine ⟨fun i => ((e i : ℕ)), fun i => hFA (Finset.mem_coe.mpr (e i).2), ?_⟩
  rw [← hsum, ← Finset.sum_coe_sort F (fun x => x)]
  exact Equiv.sum_comp e (fun x : {x // x ∈ F} => (x : ℕ))

/-- A basis of order `0` cannot exist (convention 6, exhibited rather than asserted): the
empty sum is `0`, so `1` is never representable. This is why `r = 0` needs no side condition
in `erdos_339_lower`. -/
-- @category test
theorem not_isBasisOfOrder_zero (A : Set ℕ) : ¬ IsBasisOfOrder A 0 := by
  intro h
  obtain ⟨f, -, hf⟩ := h 1
  simp at hf

/-- Degenerate case pinning down the density layer: the empty set has lower density `0`, so
`lowerDensity` is not positive by construction. -/
-- @category test
theorem lowerDensity_empty : lowerDensity (∅ : Set ℕ) = 0 := by
  have h : countingRatio (∅ : Set ℕ) = fun _ : ℕ => (0 : ℝ) := by
    funext n
    simp [countingRatio]
  rw [lowerDensity, h]
  exact liminf_const 0

/-- The companion degenerate case for the upper density. -/
-- @category test
theorem upperDensity_empty : upperDensity (∅ : Set ℕ) = 0 := by
  have h : countingRatio (∅ : Set ℕ) = fun _ : ℕ => (0 : ℝ) := by
    funext n
    simp [countingRatio]
  rw [upperDensity, h]
  exact limsup_const 0

/-! ### The `liminf`/`limsup` junk region, CLOSED (PROVED, no `sorry`)

See the header section of the same name. `Filter.liminf` is a `sSup` and `Filter.limsup` is a
`sInf` in the conditionally complete lattice `ℝ`, each of which returns the junk value `0` on an
empty or unbounded set. The eight declarations below prove that neither can happen for
`countingRatio`, so `lowerDensity` and `upperDensity` mean what their names say — in the
CONCLUSION of both main theorems, and in the HYPOTHESIS of `erdos_339_upper`. -/

/-- `|S ∩ [0,n)| / n` is never negative. Half of the range bound that closes the junk region. -/
-- @category test
theorem countingRatio_nonneg (S : Set ℕ) (n : ℕ) : 0 ≤ countingRatio S n :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- `|S ∩ [0,n)| / n ≤ 1`: a counting ratio cannot exceed one, because `S ∩ [0,n)` is a subset
of `[0,n)`, which has exactly `n` elements. The degenerate `n = 0` case is `0 / 0 = 0` under
Mathlib's division convention, which is in range and so needs no exclusion. -/
-- @category test
theorem countingRatio_le_one (S : Set ℕ) (n : ℕ) : countingRatio S n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [countingRatio]
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsub : S ∩ Set.Iio n ⊆ (↑(Finset.Iio n) : Set ℕ) := by
      intro x hx
      simpa using hx.2
    have hcard : (S ∩ Set.Iio n).ncard ≤ n := by
      have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rwa [Set.ncard_coe_finset, Nat.card_Iio] at h
    rw [countingRatio, div_le_one hn']
    exact_mod_cast hcard

/-- `lowerDensity` really is the `sSup` of this set — Mathlib's own definition of `liminf`,
pinned here so the two boundedness lemmas that follow are visibly about the right object. -/
-- @category test
theorem lowerDensity_eq_sSup (S : Set ℕ) :
    lowerDensity S = sSup {a : ℝ | ∀ᶠ n in (atTop : Filter ℕ), a ≤ countingRatio S n} :=
  Filter.liminf_eq

/-- `upperDensity` really is the `sInf` of this set (`Filter.limsup_eq`). -/
-- @category test
theorem upperDensity_eq_sInf (S : Set ℕ) :
    upperDensity S = sInf {a : ℝ | ∀ᶠ n in (atTop : Filter ℕ), countingRatio S n ≤ a} :=
  Filter.limsup_eq

/-- The set `lowerDensity` takes the `sSup` of is NONEMPTY: `0` belongs to it. -/
-- @category test
theorem liminfSet_nonempty (S : Set ℕ) :
    {a : ℝ | ∀ᶠ n in (atTop : Filter ℕ), a ≤ countingRatio S n}.Nonempty :=
  ⟨0, Filter.Eventually.of_forall fun n => countingRatio_nonneg S n⟩

/-- **The load-bearing one.** The set `lowerDensity` takes the `sSup` of is BOUNDED ABOVE, by
`1`. With `liminfSet_nonempty`, this is exactly the hypothesis under which Mathlib's `sSup` on
`ℝ` is a genuine supremum rather than its junk value `0`. -/
-- @category test
theorem liminfSet_bddAbove (S : Set ℕ) :
    BddAbove {a : ℝ | ∀ᶠ n in (atTop : Filter ℕ), a ≤ countingRatio S n} := by
  refine ⟨1, fun a ha => ?_⟩
  have ha' : ∀ᶠ n in (atTop : Filter ℕ), a ≤ countingRatio S n := ha
  obtain ⟨n, hn⟩ := ha'.exists
  exact hn.trans (countingRatio_le_one S n)

/-- The companion for `upperDensity`: the set it takes the `sInf` of is nonempty (`1` is in it).
This is the one that keeps the HYPOTHESIS of `erdos_339_upper` from being junk. -/
-- @category test
theorem limsupSet_nonempty (S : Set ℕ) :
    {a : ℝ | ∀ᶠ n in (atTop : Filter ℕ), countingRatio S n ≤ a}.Nonempty :=
  ⟨1, Filter.Eventually.of_forall fun n => countingRatio_le_one S n⟩

/-- The companion for `upperDensity`: that set is bounded BELOW, by `0`. -/
-- @category test
theorem limsupSet_bddBelow (S : Set ℕ) :
    BddBelow {a : ℝ | ∀ᶠ n in (atTop : Filter ℕ), countingRatio S n ≤ a} := by
  refine ⟨0, fun a ha => ?_⟩
  have ha' : ∀ᶠ n in (atTop : Filter ℕ), countingRatio S n ≤ a := ha
  obtain ⟨n, hn⟩ := ha'.exists
  exact (countingRatio_nonneg S n).trans hn

end Erdos339

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos339.erdos_339_lower
#print axioms Erdos339.erdos_339_upper
#print axioms Erdos339.sumsOfDistinct_subset_sumsOfExactly
#print axioms Erdos339.not_isBasisOfOrder_zero
#print axioms Erdos339.lowerDensity_empty
#print axioms Erdos339.upperDensity_empty
#print axioms Erdos339.countingRatio_nonneg
#print axioms Erdos339.countingRatio_le_one
#print axioms Erdos339.lowerDensity_eq_sSup
#print axioms Erdos339.upperDensity_eq_sInf
#print axioms Erdos339.liminfSet_nonempty
#print axioms Erdos339.liminfSet_bddAbove
#print axioms Erdos339.limsupSet_nonempty
#print axioms Erdos339.limsupSet_bddBelow
