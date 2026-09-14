/-
# Erdős problem 449 — the answer is **NO**; the resolution is a refutation

SOURCE (frozen), both nodes quoted verbatim:

QUESTION (`n000-question`):
> Let $r(n)$ count the number of $d_1,d_2$ such that $d_1\mid n$ and $d_2\mid n$ and
> $d_1<d_2<2d_1$. Is it true that, for every $\epsilon>0$,
> \[r(n) < \epsilon \tau(n)\]
> for almost all $n$, where $\tau(n)$ is the number of divisors of $n$?

RESOLUTION (`n001-resolution`):
> This is false - indeed, for any constant $K>0$ we have $r(n)>K\tau(n)$ for a positive density
> set of $n$. Kevin Ford has observed this follows from the negative solution to [448] : the
> Cauchy-Schwarz inequality implies \[r(n)+\tau(n)\geq \tau(n)^2/\tau^+(n)\] where $\tau^+(n)$ is
> as defined in [448] , and the negative solution to [448] implies the right-hand side is at least
> $(K+1)\tau(n)$ for a positive density set of $n$. (This argument is given for an essentially
> identical problem by Hall and Tenenbaum \cite{HaTe88}, Section 4.6.) See also [448] .

⚠ The question was answered **NO**. The main theorem below is therefore the RESOLUTION's sharper
positive-density statement, not the question's assertion. `erdos_449_question_answer_is_no` states
the refutation of the question itself, separately and explicitly labelled.

## Conventions the source leaves unstated (declared, not silently chosen)

1. **`r n`**: the number of *ordered* pairs `(d₁, d₂)` of divisors of `n` with `d₁ < d₂ < 2*d₁`.
   Because `d₁ < d₂` is part of the condition, each unordered pair is counted exactly once, so
   this coincides with "the number of pairs of divisors within a factor `2` of one another".
   No other reading (e.g. counting both orders) is available without contradicting `d₁ < d₂`.
2. **divisors**: `Nat.divisors n`, the *positive* divisors of `n`. For `n = 0` Mathlib makes this
   the empty finset; then `r 0 = τ 0 = 0` and `n = 0` simply fails the defining inequality of the
   density set. A single value cannot affect any density, so nothing is weakened.
3. **`τ n`**: `(Nat.divisors n).card`, the number of (positive) divisors — exactly as the source
   defines it.
4. **"positive density set"**: asymptotic **lower** density `> 0`, defined here as
   `liminf (|S ∩ [0,n)| / n)`. This is the STRONGEST of the usual readings ("positive density"
   is sometimes read as positive *upper* density, which is implied by this). ⛔ Mathlib's only
   packaged density for `ℕ` is `Schnirelmann` density, which is an **infimum over all `n ≥ 1`**,
   not a `liminf`; a Schnirelmann-positive set must be dense from the very first integer, so
   using it would state a strictly different — and here false-ish — claim. It is deliberately
   not used. Counting on `[0,n)` versus `[1,n]` does not change the `liminf`.
5. **Order of quantifiers**: the density set is allowed to depend on `K`, i.e.
   `∀ K > 0, 0 < lowerDensity {n | K * τ n < r n}`. This is the source's reading ("for any
   constant `K>0` we have ... for a positive density set of `n`"). The uniform reading (one
   single set working for every `K` simultaneously) is *not* what is claimed and is false, since
   it would force `r n = ∞` on that set.
6. **`K : ℝ`**, arbitrary positive real; the source says "constant `K > 0`". Taking `K` real
   rather than natural is the stronger statement (it includes every natural `K`).
7. **"for almost all `n`"** (question node): the exceptional set has asymptotic **upper**
   density `0`. Equivalently the good set has density `1`. Refuting this is what
   `erdos_449_question_answer_is_no` does.
8. **Strictness**: `r(n) > K τ(n)` and `r(n) < ε τ(n)` are kept strict, exactly as written.

## The `liminf`/`limsup` junk region, and why it cannot fire here (PROVED below)

`Filter.liminf f l` is `sSup {a | ∀ᶠ x in l, a ≤ f x}` and `Filter.limsup f l` is
`sInf {a | ∀ᶠ x in l, f x ≤ a}`, taken in the CONDITIONALLY complete lattice `ℝ`. Neither `sSup`
nor `sInf` is total there: on an empty set, or on a set unbounded on the relevant side, Mathlib
returns the junk value `0`, silently and with no error. That is a live hazard for a density
statement — a quantity whose true `liminf` is `+∞` would print as `0`, which would INVERT the
truth value of `erdos_449_resolution`, whose entire content is `0 < lowerDensity …`.

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
-/

-- @category research solved
-- @AMS 11
-- Category vocabulary and AMS tagging adopted from the
-- formal-conjectures corpus (509 files, measured 2026-08-28). Written as a comment
-- rather than the corpus attribute form, so this artifact still elaborates
-- standalone, outside their project.










import Mathlib
open Filter Finset

namespace Erdos449

/-- `|S ∩ [0, n)| / n`, the counting ratio whose `liminf` / `limsup` are the asymptotic
lower / upper densities of `S ⊆ ℕ`. -/
noncomputable def countingRatio (S : Set ℕ) (n : ℕ) : ℝ :=
  ((S ∩ Set.Iio n).ncard : ℝ) / (n : ℝ)

/-- Asymptotic **lower** density of a set of naturals. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ := liminf (countingRatio S) atTop

/-- Asymptotic **upper** density of a set of naturals. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ := limsup (countingRatio S) atTop

/-- `τ n` — the number of positive divisors of `n`. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- `r n` — the number of pairs `d₁, d₂` of divisors of `n` with `d₁ < d₂ < 2 d₁`. -/
def r (n : ℕ) : ℕ :=
  ((n.divisors ×ˢ n.divisors).filter (fun p => p.1 < p.2 ∧ p.2 < 2 * p.1)).card

/-- **THE RESOLUTION (main theorem).** Erdős problem 449 is answered **NO**, and sharply so:
for every constant `K > 0`, the set of `n` with `r(n) > K · τ(n)` has positive (lower) asymptotic
density. Due to Kevin Ford, via the negative solution to problem 448 and Cauchy–Schwarz. -/
theorem erdos_449_resolution (K : ℝ) (hK : 0 < K) :
    0 < lowerDensity {n : ℕ | K * (tau n : ℝ) < (r n : ℝ)} := by
  sorry

/-- **THE ORIGINAL QUESTION, ANSWERED NO.** It is *not* the case that for every `ε > 0` we have
`r(n) < ε · τ(n)` for almost all `n` (i.e. with the exceptional set of upper density `0`). -/
theorem erdos_449_question_answer_is_no :
    ¬ ∀ ε : ℝ, 0 < ε →
      upperDensity {n : ℕ | ¬ ((r n : ℝ) < ε * (tau n : ℝ))} = 0 := by
  sorry

/-! ### Anti-vacuity controls (PROVED, not part of the source)

A `sorry`-carrying statement elaborates whether or not its definitions say anything. The
lemmas below are fully proved and mention only this file's own definitions, so they are cheap
machine-checked evidence that `tau`, `r`, `countingRatio` and `lowerDensity` bite. -/

/-- Degenerate case: `1` has exactly one divisor. -/
-- @category test
theorem tau_one : tau 1 = 1 := by decide

/-- Degenerate case: `0` has no positive divisors, so `τ 0 = 0` (convention 2). -/
-- @category test
theorem tau_zero : tau 0 = 0 := by decide

/-- Degenerate case: `1` has a single divisor, so there is no pair `d₁ < d₂ < 2 d₁`. -/
-- @category test
theorem r_one : r 1 = 0 := by decide

/-- Degenerate case matching convention 2: `r 0 = τ 0 = 0`, so `n = 0` fails
`K * τ n < r n` for every `K > 0` and cannot contribute to the density set. -/
-- @category test
theorem r_zero : r 0 = 0 := by decide

/-- A NON-degenerate computation, so the controls are not all vacuous: the divisors of `6`
are `1, 2, 3, 6`, and the only pair within a factor `2` is `(2, 3)`. -/
-- @category test
theorem r_six : r 6 = 1 := by decide

/-- `r n` counts a subset of the ordered pairs of divisors, hence is at most `τ(n)²`. This is
the check that the file's `r` and `tau` really are the two quantities the source compares. -/
-- @category test
theorem r_le_tau_mul_tau (n : ℕ) : r n ≤ tau n * tau n := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp [tau]

/-- The `sInf`-free sanity check on the density layer: the empty set has lower density `0`,
so `lowerDensity` is not constantly positive by construction. -/
-- @category test
theorem lowerDensity_empty : lowerDensity (∅ : Set ℕ) = 0 := by
  have h : countingRatio (∅ : Set ℕ) = fun _ : ℕ => (0 : ℝ) := by
    funext n
    simp [countingRatio]
  rw [lowerDensity, h]
  exact liminf_const 0

/-! ### The `liminf`/`limsup` junk region, CLOSED (PROVED, no `sorry`)

See the header section of the same name. `Filter.liminf` is a `sSup` and `Filter.limsup` is a
`sInf` in the conditionally complete lattice `ℝ`, each of which returns the junk value `0` on an
empty or unbounded set. The six declarations below prove that neither can happen for
`countingRatio`, so `lowerDensity` and `upperDensity` mean what their names say. -/

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

/-- The companion for `upperDensity`: the set it takes the `sInf` of is nonempty (`1` is in it). -/
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

end Erdos449

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos449.erdos_449_resolution
#print axioms Erdos449.erdos_449_question_answer_is_no
#print axioms Erdos449.tau_one
#print axioms Erdos449.tau_zero
#print axioms Erdos449.r_one
#print axioms Erdos449.r_zero
#print axioms Erdos449.r_six
#print axioms Erdos449.r_le_tau_mul_tau
#print axioms Erdos449.lowerDensity_empty
#print axioms Erdos449.countingRatio_nonneg
#print axioms Erdos449.countingRatio_le_one
#print axioms Erdos449.lowerDensity_eq_sSup
#print axioms Erdos449.upperDensity_eq_sInf
#print axioms Erdos449.liminfSet_nonempty
#print axioms Erdos449.liminfSet_bddAbove
#print axioms Erdos449.limsupSet_nonempty
#print axioms Erdos449.limsupSet_bddBelow
