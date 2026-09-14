/-
# Erdős problem #604 — the pinned distinct-distances problem  (**OPEN**, $500 prize)

## The question (verbatim from the frozen source, node `n000-question`)

> Given $n$ distinct points $A\subset\mathbb{R}^2$ must there be a point $x\in A$ such that
> \[\#\{ d(x,y) : y \in A\} \gg n^{1-o(1)}?\]
> Or even $\gg n/\sqrt{\log n}$?

## The resolution node (verbatim, node `n001-resolution`)

> The pinned distance problem, a stronger form of [89] . The example of an integer grid show that
> $n/\sqrt{\log n}$ would be best possible. It may be true that there are $\gg n$ many such points
> (Hunter has noted in the comments that this trivially follows from the existence of a single
> point), or that this is true on average - for example, if $d(x)$ counts the number of distinct
> distances from $x$ then in \cite{Er75f} Erdős conjectured
> \[\sum_{x\in A}d(x) \gg \frac{n^2}{\sqrt{\log n}},\]
> where $A\subset \mathbb{R}^2$ is any set of $n$ points. In \cite{Er97e} Erdős offers \$500 for a
> solution to this problem, but it is unclear whether he intended this for proving the existence of
> a single such point or for $\gg n$ many such points. In \cite{Er97e} Erdős wrote that he initially
> 'overconjectured' and thought that the answer to this problem is the same as for the number of
> distinct distances between all pairs (see [89] ), but this was disproved by Harborth. It could be
> true that the answers are the same up to an additive factor of $n^{o(1)}$. The best known bound is
> \[\gg n^{c-o(1)},\]
> due to Katz and Tardos \cite{KaTa04}, where
> \[c=\frac{48-14e}{55-16e}=0.864137\cdots.\]

## What is formalized here — and what is deliberately NOT

**This problem is OPEN.**  Accordingly this file states the QUESTION and asserts no answer to it:
`Erdos604.Question` and `Erdos604.QuestionSharp` are `def ... : Prop`, never theorems.  Nothing in
this file proves, disproves, or presupposes either.  There is no `erdos_604_resolution`.

What *is* stated as a `theorem` (each with `sorry`, each labelled with the source that records it):

* `katz_tardos_lower_bound` — the best known lower bound, `≫ n^{c-o(1)}`, `c = (48-14e)/(55-16e)`.
* `integer_grid_upper_bound` — the integer-grid construction, which is why `n/√log n` is the
  best one could possibly hope for.
* `many_points_of_single` — Hunter's recorded remark that the `≫ n`-many-points form follows
  from the single-point form.

The remaining two *questions* the resolution node records (the `≫ n` many points form, and Erdős's
`Er75f` average-case conjecture) are likewise `def ... : Prop` — they are conjectures, not results.

## Conventions the source leaves unstated (each one NAMED, with the reading taken)

* **The plane.**  `EuclideanSpace ℝ (Fin 2)`, i.e. the ℓ² metric.  ⛔ *Not* `ℝ × ℝ`, which in
  Mathlib carries the **sup** metric: `dist (a₁,a₂) (b₁,b₂) = max |a₁-b₁| |a₂-b₂|`.  Under the sup
  metric circles are squares and the distinct-distance incidence geometry is a different problem.
* **`d(x,x)` is counted.**  The source writes `#{ d(x,y) : y ∈ A }` with `y` ranging over all of
  `A`, and `x ∈ A`, so the value `d(x,x) = 0` is in the set.  We take the source literally: the
  count includes `0`.  This shifts the quantity by exactly `1` versus the "`y ≠ x`" reading, which
  is invisible at the asymptotic scale the question asks about (`n^{1-o(1)}`, `n/√log n`) and
  matters only for the degenerate small cases — where it is pinned down here by
  `maxPinnedDistances_pair`, which gives `2` for a two-point set (namely `{0, d(p,q)}`).
* **"must there be a point `x ∈ A`".**  Read as the maximum over `x ∈ A` of the pinned count:
  `maxPinnedDistances A = A.sup (pinnedDistances A)`.  `Finset.sup` on `ℕ` returns `0` on the empty
  set, which is the correct degenerate value.
* **`≫` (Vinogradov).**  `f(n) ≫ g(n)` is read as: `∃ C > 0` such that `f n ≥ C * g n` for all
  sufficiently large `n` (`∀ᶠ n in atTop`).  The implicit constant is existentially quantified and
  no uniformity beyond that is claimed.
* **Asymptotic in `n`, uniform over point sets.**  The question asks about *every* `n`-point set,
  so each statement is `∀ᶠ n in atTop, ∀ A : Finset Plane, A.card = n → ...`.  The `∀ A` sits
  *inside* the eventually, so the constant `C` does not depend on `A`.
* **`n^{1-o(1)}`.**  Read as: for every `ε > 0` there is `C > 0` with eventually
  `maxPinnedDistances A ≥ C * n^{1-ε}`.  ⛔ This is *not* any Mathlib `Asymptotics.IsLittleO`
  statement: there is no little-o that lives inside an exponent.  The `∀ ε > 0` unfolding is the
  faithful form.  (Note the quantifier order: `ε` first, then `C` — `C` is allowed to depend on
  `ε`, which is what `n^{1-o(1)}` means.)
* **`n^{c-o(1)}`** in Katz–Tardos is unfolded the same way, with `1` replaced by `c`.
* **"distinct points"** is the content of `A : Finset Plane` together with `A.card = n`; a `Finset`
  has no repeats, so no extra hypothesis is needed.
* **`log`** is the natural logarithm (`Real.log`), and `√` is `Real.sqrt`.  For small `n` the
  expression `n/√(log n)` is ill-behaved (`log 1 = 0`), which is exactly why every asymptotic
  statement is guarded by `∀ᶠ n in atTop` rather than `∀ n`.
-/

-- @category research open
-- @AMS 52
-- Category vocabulary and AMS tagging adopted from the formal-conjectures corpus
-- (509 files, measured 2026-08-28). Written as a comment rather than the corpus
-- attribute form, so this artifact still elaborates standalone, outside their project.








import Mathlib
namespace Erdos604

open Filter

/-- The Euclidean plane `ℝ²` with its ℓ² metric.  (NOT `ℝ × ℝ`, which carries the sup metric.) -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- `pinnedDistances A x` is `#{ d(x,y) : y ∈ A }`, the number of **distinct** distances from the
pin `x` to the points of `A`.

Taken literally from the source: `y` ranges over all of `A`, so when `x ∈ A` the value
`d(x,x) = 0` is one of the counted distances. -/
noncomputable def pinnedDistances (A : Finset Plane) (x : Plane) : ℕ :=
  ((fun y => dist x y) '' (A : Set Plane)).ncard

/-- `maxPinnedDistances A = max_{x ∈ A} #{ d(x,y) : y ∈ A }`.

This is the quantity Erdős's "must there be a point `x ∈ A` such that ..." asks to bound below.
On `A = ∅` it is `0`. -/
noncomputable def maxPinnedDistances (A : Finset Plane) : ℕ :=
  A.sup (pinnedDistances A)

/-! ### Anti-vacuity controls — PROVED (no `sorry`), exercising the definitions above -/

/-- A pinned count never exceeds the number of points: at most one distance per point of `A`. -/
theorem pinnedDistances_le_card (A : Finset Plane) (x : Plane) :
    pinnedDistances A x ≤ A.card := by
  unfold pinnedDistances
  calc ((fun y => dist x y) '' (A : Set Plane)).ncard
      ≤ (A : Set Plane).ncard := Set.ncard_image_le A.finite_toSet
    _ = A.card := Set.ncard_coe_finset A

/-- Hence the maximum pinned count is at most the number of points. -/
theorem maxPinnedDistances_le_card (A : Finset Plane) :
    maxPinnedDistances A ≤ A.card :=
  Finset.sup_le fun x _ => pinnedDistances_le_card A x

/-- Degenerate case: the empty set has no pin, so the quantity is `0`. -/
theorem maxPinnedDistances_empty : maxPinnedDistances (∅ : Finset Plane) = 0 := by
  simp [maxPinnedDistances]

/-- Two distinct points give exactly `2`, namely the distances `{0, d(p,q)}`.

This is the small case that pins down the `d(x,x) = 0` counting convention: under the "`y ≠ x`"
reading the answer would be `1`. -/
theorem maxPinnedDistances_pair [DecidableEq Plane] {p q : Plane} (h : p ≠ q) :
    maxPinnedDistances ({p, q} : Finset Plane) = 2 := by
  have hpq : dist p q ≠ 0 := dist_ne_zero.mpr h
  have hqp : dist q p ≠ 0 := dist_ne_zero.mpr h.symm
  have hp : pinnedDistances ({p, q} : Finset Plane) p = 2 := by
    have : ((fun y => dist p y) '' (({p, q} : Finset Plane) : Set Plane))
        = ({0, dist p q} : Set ℝ) := by
      simp [Set.image_insert_eq, Set.image_singleton]
    rw [pinnedDistances, this, Set.ncard_pair (Ne.symm hpq)]
  have hq : pinnedDistances ({p, q} : Finset Plane) q = 2 := by
    have : ((fun y => dist q y) '' (({p, q} : Finset Plane) : Set Plane))
        = ({dist q p, 0} : Set ℝ) := by
      simp [Set.image_insert_eq, Set.image_singleton]
    rw [pinnedDistances, this, Set.ncard_pair hqp]
  rw [maxPinnedDistances, Finset.sup_insert, Finset.sup_singleton, hp, hq]
  simp

/-! ### THE QUESTION.  Both forms are OPEN; neither is asserted here. -/

/-- **Erdős #604, first form (OPEN).**  *Given `n` distinct points `A ⊆ ℝ²` must there be a point
`x ∈ A` such that `#{ d(x,y) : y ∈ A } ≫ n^{1-o(1)}`?*

Unfolded: for every `ε > 0` there is an implicit constant `C > 0` such that every sufficiently
large finite planar point set `A` of size `n` has some pin with at least `C·n^{1-ε}` distinct
distances to `A`.

This is a `def`, not a `theorem`: the problem is open and this file takes no position on it. -/
def Question : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ A : Finset Plane, A.card = n →
      C * (n : ℝ) ^ ((1 : ℝ) - ε) ≤ (maxPinnedDistances A : ℝ)

/-- **Erdős #604, sharper form (OPEN).**  *Or even `≫ n/√(log n)`?*

The resolution node records that the integer grid shows this would be best possible; see
`integer_grid_upper_bound`.  Again a `def`, not a `theorem`. -/
def QuestionSharp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ A : Finset Plane, A.card = n →
      C * (n : ℝ) / Real.sqrt (Real.log n) ≤ (maxPinnedDistances A : ℝ)

/-- **The `≫ n` many points variant (OPEN).**  *"It may be true that there are `≫ n` many such
points."*  Read as: for every `ε > 0` there are constants `c, C > 0` such that eventually every
`n`-point set has at least `c·n` pins each achieving `C·n^{1-ε}` distinct distances. -/
def QuestionManyPoints : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ A : Finset Plane, A.card = n →
      c * (n : ℝ) ≤
        ({x ∈ (A : Set Plane) |
          C * (n : ℝ) ^ ((1 : ℝ) - ε) ≤ (pinnedDistances A x : ℝ)}.ncard : ℝ)

/-- **Erdős's average-case conjecture, `Er75f` (OPEN).**  *If `d(x)` counts the number of distinct
distances from `x` then `∑_{x ∈ A} d(x) ≫ n²/√(log n)`.*

A conjecture recorded by the source, hence a `def`, not a `theorem`. -/
def QuestionAverage : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ∀ A : Finset Plane, A.card = n →
      C * (n : ℝ) ^ (2 : ℕ) / Real.sqrt (Real.log n)
        ≤ ((∑ x ∈ A, pinnedDistances A x : ℕ) : ℝ)

/-! ### Bounds the source records as KNOWN.  Each is `sorry`: stated, not proved here. -/

/-- The Katz–Tardos exponent `c = (48 - 14e)/(55 - 16e) = 0.864137⋯`. -/
noncomputable def katzTardosExponent : ℝ :=
  (48 - 14 * Real.exp 1) / (55 - 16 * Real.exp 1)

/-- Sanity, PROVED: the Katz–Tardos exponent is a genuine exponent strictly between `0` and `1`,
so `katz_tardos_lower_bound` really is weaker than `Question` and does not settle it. -/
theorem katzTardosExponent_mem_Ioo :
    0 < katzTardosExponent ∧ katzTardosExponent < 1 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hden : (0 : ℝ) < 55 - 16 * Real.exp 1 := by nlinarith
  have hnum : (0 : ℝ) < 48 - 14 * Real.exp 1 := by nlinarith
  unfold katzTardosExponent
  refine ⟨div_pos hnum hden, ?_⟩
  rw [div_lt_one hden]
  linarith

/-- **Best known bound (Katz–Tardos, `KaTa04`).**  `max_x #{ d(x,y) : y ∈ A } ≫ n^{c-o(1)}` with
`c = (48-14e)/(55-16e)`.

⛔ This does NOT answer `Question`: `c < 1` (see `katzTardosExponent_mem_Ioo`), so it is strictly
weaker than the `n^{1-o(1)}` the problem asks for. -/
theorem katz_tardos_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ A : Finset Plane, A.card = n →
        C * (n : ℝ) ^ (katzTardosExponent - ε) ≤ (maxPinnedDistances A : ℝ) := by
  sorry

/-- **The integer grid (source: "the example of an integer grid show that `n/√log n` would be best
possible").**  There are arbitrarily large `n`-point sets in which *every* pin sees only
`O(n/√(log n))` distinct distances.

Consequence: `QuestionSharp` is the strongest form that could hold; no bound above
`n/√(log n)` is available. -/
theorem integer_grid_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∃ A : Finset Plane, A.card = n ∧
        (maxPinnedDistances A : ℝ) ≤ C * (n : ℝ) / Real.sqrt (Real.log n) := by
  sorry

/-- **Hunter's recorded remark**: the `≫ n`-many-points form *"trivially follows from the existence
of a single point"*.  Stated as the source states it; not proved here. -/
theorem many_points_of_single : Question → QuestionManyPoints := by
  sorry

/-- The sharper form implies the first, since `n/√(log n) ≥ n^{1-ε}` eventually for every
`ε > 0`.  Recorded so that the two `def`s above are not read as independent questions. -/
theorem questionSharp_imp_question : QuestionSharp → Question := by
  sorry

end Erdos604

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos604.pinnedDistances_le_card
#print axioms Erdos604.maxPinnedDistances_le_card
#print axioms Erdos604.maxPinnedDistances_empty
#print axioms Erdos604.maxPinnedDistances_pair
#print axioms Erdos604.katzTardosExponent_mem_Ioo
#print axioms Erdos604.katz_tardos_lower_bound
#print axioms Erdos604.integer_grid_upper_bound
#print axioms Erdos604.many_points_of_single
#print axioms Erdos604.questionSharp_imp_question
