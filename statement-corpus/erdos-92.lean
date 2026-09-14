/-
# Erdős problem #92 — the equidistant-degree function `f(n)` of planar point sets

## The question (verbatim from the frozen source, node `n000-question`)

> Let $f(n)$ be maximal such that there exists a set $A$ of $n$ points in $\mathbb{R}^2$ in which
> every $x\in A$ has at least $f(n)$ points in $A$ equidistant from $x$. Is it true that
> $f(n)\leq n^{o(1)}$? Or even $f(n) < n^{O(1/\log\log n)}$?

## The resolution (verbatim, node `n001-resolution`)

> This is a stronger form of the unit distance conjecture (see [90]). As such the recent disproof
> of [90] also disproves this. The set of lattice points imply $f(n) > n^{c/\log\log n}$ for some
> constant $c>0$. ... It is trivial that $f(n) \ll n^{1/2}$. A result of Pach and Sharir
> (Theorem 4 of [PaSh92]) implies $f(n) \ll n^{2/5}$. Hunter has observed that the circle-point
> incidence bound of Janzer, Janzer, Methuku, and Tardos [JJMT24] implies $f(n) \ll n^{4/11}$.
> Fishburn (personal communication to Erdős, later published in [ErFi97]) proved that $6$ is the
> smallest $n$ such that $f(n)=3$ and $8$ is the smallest $n$ such that $f(n)=4$, and suggested
> that the lattice points may not be best example.

## What is formalized here

The headline theorem is `erdos_92_resolution`: the answer to Erdős's question is **NO**.
`f(n) ≤ n^{o(1)}` is FALSE.  Everything else in this file is a supporting statement that the
resolution node also asserts, kept separate so that no bound is silently folded into the headline.

Every statement carries `sorry`: this file is a faithful *statement* of the resolution, not a
proof of it.  The proof is the disproof of Erdős #90 (the unit distance conjecture), which is not
reproduced here.

## Conventions the source leaves unstated (each one NAMED)

* **"points equidistant from x"** — read as: there is a single radius `r` with at least `k` points
  of `A` at distance exactly `r` from `x`.  We require `0 < r`, which automatically excludes `x`
  itself from its own count.  Taking `r = 0` would contribute a count of exactly `1`, so this
  convention is invisible for every `k ≥ 2` and only pins down the degenerate small cases.
* **`x` itself is not counted** — forced by `0 < r` above.  Erdős's `f(6) = 3`, `f(8) = 4`
  (Fishburn) are consistent with this reading and not with the `x`-counting one.
* **`f(n)` as a supremum** — "maximal such that there exists a set A" is read as
  `sSup {k | ∃ A, A.card = n ∧ ∀ x ∈ A, x has ≥ k equidistant points}`.  The set is bounded above
  by `n`, so the supremum is attained and `sSup` on `ℕ` is the honest max.
* **`f(n) ≤ n^{o(1)}`** — read as: `∀ ε > 0, eventually (in n) f n ≤ n ^ ε`.  This is the standard
  meaning of `g(n) = n^{o(1)}` for `g ≥ 1`: it says `log (f n) / log n → 0`, and since `f n ≥ 1`
  the quotient is non-negative, so one-sided domination by `n^ε` for every `ε > 0` is exactly
  equivalent.  `o(1)` sits in the EXPONENT, so this is *not* any Mathlib `IsLittleO` statement.
* **`f(n) < n^{O(1/log log n)}`** — read as: `∃ C > 0, eventually f n < n ^ (C / log log n)`.
* **`≪`** — Vinogradov: `∃ C > 0, eventually f n ≤ C * n^α`.  Implicit constant, no uniformity
  claim beyond that.
* **The plane** — `EuclideanSpace ℝ (Fin 2)`, i.e. the ℓ² metric.

## Mathlib near-misses recorded (traps avoided)

1. **`ℝ × ℝ` carries the SUP metric, not the Euclidean one.**  `dist (a₁,a₂) (b₁,b₂)` on a product
   in Mathlib is `max |a₁-b₁| |a₂-b₂|`.  Formalizing "equidistant" over `ℝ × ℝ` would state a
   *different, ℓ^∞ problem* — circles become squares and the whole incidence geometry changes.
   `EuclideanSpace ℝ (Fin 2)` (or `ℂ`) is the correct carrier.
2. **`Asymptotics.IsLittleO` is the wrong tool for `n^{o(1)}`.**  `f =o[atTop] id` says
   `f n / n → 0`, which is implied by (and far weaker than) `f n ≤ n^{o(1)}`; and there is no
   Mathlib little-o that lives inside an exponent.  The `∀ ε > 0` unfolding below is the faithful
   form.  Reaching for `IsLittleO` here is the same class of mistake as substituting Schnirelmann
   density for asymptotic density.
3. **`Finset.sup` vs `sSup`.**  `Finset.sup` would need the index set of candidate `k` to be a
   `Finset`; `sSup` on `ℕ` (`Nat.instConditionallyCompleteLinearOrderBot`) is the right notion and
   returns `0` on the empty set, which is the correct value for the vacuous cases.
-/

-- @category research solved
-- @AMS 52
-- Category vocabulary and AMS tagging adopted from the
-- formal-conjectures corpus (509 files, measured 2026-08-28). Written as a comment
-- rather than the corpus attribute form, so this artifact still elaborates
-- standalone, outside their project.







import Mathlib
namespace Erdos92

open Filter

/-- The Euclidean plane `ℝ²` with its ℓ² metric.  (NOT `ℝ × ℝ`, which carries the sup metric.) -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- `HasEquidistantDegree A k` : every point `x` of the finite planar set `A` has at least `k`
points of `A` equidistant from it — i.e. there is a common radius `r > 0` such that at least `k`
points of `A` lie at distance exactly `r` from `x`.

The radius is required to be positive, so `x` never counts towards its own degree. -/
def HasEquidistantDegree (A : Finset Plane) (k : ℕ) : Prop :=
  ∀ x ∈ A, ∃ r : ℝ, 0 < r ∧ k ≤ {y ∈ (A : Set Plane) | dist x y = r}.ncard

/-- Erdős's `f(n)`: the largest `k` for which some `n`-point planar set has every point carrying
at least `k` equidistant companions. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset Plane, A.card = n ∧ HasEquidistantDegree A k}

/-- Sanity: the candidate set defining `f n` is bounded above by `n`, so `f` is a genuine maximum
rather than a `sSup` of an unbounded set. -/
theorem f_le_self (n : ℕ) : f n ≤ n := by
  sorry

/-- Erdős's first question, stated: `f(n) ≤ n^{o(1)}`.

Faithful reading of `n^{o(1)}`: for every `ε > 0`, eventually `f n ≤ n ^ ε`. -/
def LittleOneExponent : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ ε

/-- Erdős's second, sharper question, stated: `f(n) < n^{O(1/log log n)}`. -/
def BigOhLogLogExponent : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (f n : ℝ) < (n : ℝ) ^ (C / Real.log (Real.log (n : ℝ)))

/-- **THE RESOLUTION.**  The answer to Erdős's question is NO.

Problem #92 is a strengthening of the unit distance conjecture (Erdős #90); the recent disproof of
#90 therefore also disproves this.  `f(n) ≤ n^{o(1)}` is FALSE. -/
theorem erdos_92_resolution : ¬ LittleOneExponent := by
  sorry

/-- The same resolution in positive form: `f(n)` is infinitely often at least a fixed positive
power of `n`.  This is the direct negation of `LittleOneExponent` and is the strongest form of the
disproof that the source supports (the source names no explicit exponent). -/
theorem erdos_92_resolution_positive :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop, (n : ℝ) ^ c ≤ (f n : ℝ) := by
  sorry

/-- The sharper question is a *strengthening* of the first (since `1/log log n → 0`), so the
disproof kills it too. -/
theorem sharper_implies_littleOne : BigOhLogLogExponent → LittleOneExponent := by
  sorry

/-- Consequently Erdős's second, sharper question is also answered NO. -/
theorem erdos_92_resolution_sharper : ¬ BigOhLogLogExponent := fun h =>
  erdos_92_resolution (sharper_implies_littleOne h)

/-! ### The surviving bounds asserted by the resolution node -/

/-- The lattice-point construction: `f(n) > n^{c/log log n}` for some `c > 0`.

Note this is *weaker* than `erdos_92_resolution_positive` and does **not** on its own disprove
either form of the question — the exponent still tends to `0`.  It is stated separately precisely
so that it is never mistaken for the disproof. -/
theorem erdos_92_lattice_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (c / Real.log (Real.log (n : ℝ))) < (f n : ℝ) := by
  sorry

/-- Trivial upper bound: `f(n) ≪ n^{1/2}`. -/
theorem erdos_92_trivial_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

/-- Pach–Sharir (Theorem 4 of `PaSh92`) implies `f(n) ≪ n^{2/5}`. -/
theorem erdos_92_pach_sharir_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / 5) := by
  sorry

/-- Hunter's observation: the circle-point incidence bound of Janzer, Janzer, Methuku and Tardos
(`JJMT24`) implies `f(n) ≪ n^{4/11}`.  This is the best upper bound the source records. -/
theorem erdos_92_hunter_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 11) := by
  sorry

/-- Fishburn: `6` is the smallest `n` with `f(n) = 3`. -/
theorem erdos_92_fishburn_three : f 6 = 3 ∧ ∀ n < 6, f n ≠ 3 := by
  sorry

/-- Fishburn: `8` is the smallest `n` with `f(n) = 4`. -/
theorem erdos_92_fishburn_four : f 8 = 4 ∧ ∀ n < 8, f n ≠ 4 := by
  sorry

end Erdos92

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos92.f_le_self
#print axioms Erdos92.erdos_92_resolution
#print axioms Erdos92.erdos_92_resolution_positive
#print axioms Erdos92.sharper_implies_littleOne
#print axioms Erdos92.erdos_92_resolution_sharper
#print axioms Erdos92.erdos_92_lattice_lower_bound
#print axioms Erdos92.erdos_92_trivial_upper
#print axioms Erdos92.erdos_92_pach_sharir_upper
#print axioms Erdos92.erdos_92_hunter_upper
#print axioms Erdos92.erdos_92_fishburn_three
#print axioms Erdos92.erdos_92_fishburn_four
