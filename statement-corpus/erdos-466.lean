/-
# Erdős problem 466 — points in a disc with pairwise distances far from integers

SOURCE (frozen), `entry-graph-erdos-466.json`, node `n000-question` (kind: question):

  "Let $N(X,\delta)$ denote the maximum number of points $P_1,\ldots,P_n$ which can be chosen
   in a circle of radius $X$ such that \[\| \lvert P_i-P_j\rvert \| \geq \delta\] for all
   $1\leq i<j\leq n$. (Here $\|x\|$ is the distance from $x$ to the nearest integer.)
   Is there some $\delta>0$ such that \[\lim_{x\to \infty}N(X,\delta)=\infty?\]"

SOURCE node `n001-resolution` (kind: resolution):

  "Graham proved this is true, and in fact \[N(X,1/10)> \frac{\log X}{10}.\] This was
   substantially improved by S\'{a}rk\"{o}zy \cite{Sa76}, who proved that for, all sufficiently
   small $\delta>0$, \[N(X,\delta)>X^{1/2-\delta^{1/7}}.\] See also [465] for upper bounds and
   [953] for a similar problem."

Two results are formalized below, separately and without merging:
  * `graham_lower_bound`  : N(X, 1/10) > (log X)/10
  * `sarkozy_lower_bound` : for all sufficiently small δ > 0, N(X, δ) > X^(1/2 − δ^(1/7))
and, as the answer to Erdős's question itself, `erdos_466_answer`.

--------------------------------------------------------------------------------------------
CONVENTIONS THE SOURCE LEAVES UNSTATED — every one named, with the reading taken.

(1) "circle of radius X" = the CLOSED DISC of radius X, not the circumference.
    Erdős writes points chosen *in* a circle, and the companion entry [465] on upper bounds is
    a plane-packing statement; a 1-dimensional circumference reading makes N a question about
    chord lengths, which is not what "in" says. HONESTY NOTE: for a LOWER bound this is the
    weaker of the two readings — the disc gives more room to place points, so the disc version
    of each theorem is implied by (and does not imply) the circumference version. The reading
    is taken because it is the intended one, and the weakening is recorded here explicitly.

(2) Centre of the disc. Unstated. Taken as the origin. This is genuinely WLOG and costs
    nothing: the constraint depends only on the pairwise distances `dist Pᵢ Pⱼ`, which are
    translation invariant, so N is the same for every centre.

(3) "maximum number of points" — the points are indexed P₁,…,Pₙ with the condition imposed
    for i < j. They are automatically distinct: coincident points give ‖0‖ = 0 < δ. So a
    `Finset` of cardinality n is a faithful (and equivalent) encoding, with the symmetric
    condition imposed on all pairs P ≠ Q.

(4) Range of X. Neither bound can hold for every X > 0 as stated (Sárközy's is an asymptotic
    result and Graham's is stated without a range), so both are formalized in the standard
    "for all sufficiently large X" form, `∀ᶠ X in atTop`. For Graham this is a mild weakening
    of a bound that plausibly holds for all X ≥ 1; the eventual form is what the source
    supports. In Sárközy's case the threshold in X is allowed to depend on δ, which is the
    only reading under which the quoted inequality can hold.

(5) "for all sufficiently small δ > 0" = ∃ δ₀ > 0, ∀ δ ∈ (0, δ₀). Standard.

(6) `lim_{x→∞}` in the question is written with a lowercase x while the function is N(X,δ);
    read as X → ∞.

(7) Strictness: the separation condition is `≥ δ` (non-strict, as printed); both bounds on N
    are strict `>` (as printed).

--------------------------------------------------------------------------------------------
NEAR-MISS TRAPS IN MATHLIB (recorded).

  * `Int.fract x` is the FRACTIONAL PART, and is NOT ‖x‖. The distance to the nearest integer
    is `min (Int.fract x) (1 - Int.fract x)`; `Int.fract (0.9) = 0.9` while ‖0.9‖ = 0.1.
    Using `Int.fract` would silently change the problem. We define `nearestIntDist x` as
    `|x - round x|` and PROVE the `min` characterisation below (`nearestIntDist_eq_min`,
    no `sorry`) so the definition is pinned to Mathlib's own lemma `abs_sub_round_eq_min`.
  * Mathlib's own idiom for ‖·‖ is the norm on `AddCircle 1`: `UnitAddCircle.norm_eq` states
    `‖(x : AddCircle 1)‖ = |x - round x|`, i.e. exactly our definition. We use the plain real
    form to keep imports small; the two agree definitionally-up-to-that-lemma.
  * The plane must be `EuclideanSpace ℝ (Fin 2)`. `ℝ × ℝ` carries the SUP metric in Mathlib,
    so `dist` on `ℝ × ℝ` is max|Δx|,|Δy| — not the Euclidean distance the problem means.
    That substitution would change every distance in the statement.
  * `round` in Mathlib is round-half-up, but `|x - round x|` is the distance to the nearest
    integer regardless of the half-integer tie-break, so no convention leaks in.

--------------------------------------------------------------------------------------------
THE `Nat.sSup` JUNK REGION IN `N`, AND WHY IT CANNOT FIRE (PROVED BELOW, no `sorry`).

`N X δ` is a `sSup` over `{n | ∃ S, IsAdmissible X δ S ∧ S.card = n}`, and `sSup` on `ℕ` is NOT
total: on an unbounded (or empty) set Mathlib returns the junk value `0`, silently. Every main
theorem here is a LOWER bound on `N`, so this is not a cosmetic hazard — if that set were
unbounded, `N` would be `0` and `graham_lower_bound`, `sarkozy_lower_bound` and
`erdos_466_answer` would all be FALSE as stated, not merely awkward.

⛔ It is not unbounded, and the argument is now machine-checked rather than assumed:

  (a) `nearestIntDist x ≤ x` for `x ≥ 0` (`nearestIntDist_le_self`), because for `0 ≤ x` the
      fractional part `Int.fract x` is at most `x`. Hence an admissible pair of distinct points
      satisfies `δ ≤ ‖dist P Q‖ ≤ dist P Q`: the separation condition on ‖·‖, which by itself
      only says distances avoid neighbourhoods of the integers, does force genuine Euclidean
      separation by `δ` (`dist_ge_of_isAdmissible`).
  (b) A closed disc in `EuclideanSpace ℝ (Fin 2)` is compact, hence TOTALLY BOUNDED: it is
      covered by finitely many balls of radius `δ/2`, by a finite set depending only on `X` and
      `δ`. Each admissible point lies in one of them, and by (a) no two distinct admissible
      points share one (they would then be less than `δ` apart). So the cover's cardinality is a
      uniform bound on `S.card` (`exists_bound_card_isAdmissible`) — this is the packing
      argument, run through total boundedness rather than through a volume computation.
  (c) Therefore the set is `BddAbove` (`admissibleCards_bddAbove`, for `δ > 0`) and `Nonempty`
      (`admissibleCards_nonempty`, witnessed by `S = ∅`, `n = 0`), so `N` is a genuine maximum
      and `le_csSup` applies: `card_le_N_of_isAdmissible`.

⛔ THE BOUNDEDNESS NEEDS `δ > 0`, AND THAT IS NOT AN ARTEFACT. At `δ = 0` the condition is
vacuous and, for `X ≥ 0`, `{n | ∃ S, …}` really is unbounded, so `N X 0 = 0` really is Mathlib
junk. (For `X < 0` the disc is empty and `N X 0 = 0` is the honest answer, not junk.) Both
formalized bounds and the question instantiate `δ > 0` (`1/10`, and `0 < δ < δ₀`), so no theorem
in this file touches the junk region. That restriction is stated here rather than left implicit.

The `_witness` variants were written to avoid depending on the well-definedness of this `sSup`,
and they are KEPT — they are the stronger statements, since a witness exhibits the configuration.
`graham_witness_imp_bound` is the proved bridge showing the witness form now implies the `N`
form; before the boundedness lemmas above, that implication was not available.
-/

-- @category research solved
-- @AMS 11
-- Category vocabulary and AMS tagging adopted from the
-- formal-conjectures corpus (509 files, measured 2026-08-28). Written as a comment
-- rather than the corpus attribute form, so this artifact still elaborates
-- standalone, outside their project.






import Mathlib
open Filter

namespace Erdos466

/-- `‖x‖` in the source: the distance from `x` to the nearest integer. -/
noncomputable def nearestIntDist (x : ℝ) : ℝ := |x - round x|

/-- Pins the definition to the intended object and separates it from `Int.fract`. -/
theorem nearestIntDist_eq_min (x : ℝ) :
    nearestIntDist x = min (Int.fract x) (1 - Int.fract x) :=
  abs_sub_round_eq_min x

/-- The plane. `EuclideanSpace ℝ (Fin 2)`, so that `dist` is the Euclidean distance. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- `S` is an admissible configuration for `N(X, δ)`: a finite set of points of the closed
disc of radius `X` centred at the origin, any two distinct members of which are at a distance
whose distance to the nearest integer is at least `δ`. -/
def IsAdmissible (X δ : ℝ) (S : Finset Plane) : Prop :=
  (∀ P ∈ S, dist P 0 ≤ X) ∧
    ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → δ ≤ nearestIntDist (dist P Q)

/-- `N X δ` : the maximum number of points that can be chosen in a (closed) disc of radius `X`
so that the distance between any two of them is at least `δ` away from every integer. -/
noncomputable def N (X δ : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ S : Finset Plane, IsAdmissible X δ S ∧ S.card = n}

/-! ### Theorem 1 — Graham -/

/-- **Graham.** `N(X, 1/10) > (log X)/10` for all sufficiently large `X`. -/
theorem graham_lower_bound :
    ∀ᶠ X : ℝ in atTop, Real.log X / 10 < (N X (1 / 10) : ℝ) := by
  sorry

/-- **Graham, unpacked.** The same content stated as the existence of the configuration, so
that the result does not depend on the well-definedness of the supremum in `N`. -/
theorem graham_lower_bound_witness :
    ∀ᶠ X : ℝ in atTop,
      ∃ S : Finset Plane, IsAdmissible X (1 / 10) S ∧ Real.log X / 10 < (S.card : ℝ) := by
  sorry

/-! ### Theorem 2 — Sárközy (substantially stronger; a different, and larger, family of δ) -/

/-- **Sárközy (1976).** For all sufficiently small `δ > 0`, `N(X, δ) > X^(1/2 − δ^(1/7))`
for all sufficiently large `X` (the threshold in `X` may depend on `δ`). Here both powers are
real exponentiation `Real.rpow`. -/
theorem sarkozy_lower_bound :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ᶠ X : ℝ in atTop, X ^ ((1 : ℝ) / 2 - δ ^ ((1 : ℝ) / 7)) < (N X δ : ℝ) := by
  sorry

/-- **Sárközy, unpacked**, as the existence of the configuration. -/
theorem sarkozy_lower_bound_witness :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ᶠ X : ℝ in atTop, ∃ S : Finset Plane,
        IsAdmissible X δ S ∧ X ^ ((1 : ℝ) / 2 - δ ^ ((1 : ℝ) / 7)) < (S.card : ℝ) := by
  sorry

/-! ### Erdős's question, and its (affirmative) answer -/

/-- Erdős's question: is there some `δ > 0` with `N(X, δ) → ∞` as `X → ∞`? -/
def Question : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun X : ℝ => N X δ) atTop atTop

/-- **Yes** — this is what Graham proved; it also follows from Sárközy's stronger bound. -/
theorem erdos_466_answer : Question := by
  sorry

/-! ### The `Nat.sSup` junk region in `N`, CLOSED (PROVED, no `sorry`)

See the header section of the same name. These are also this file's anti-vacuity controls: they
are fully proved, mention only this file's own definitions, and are what makes `N` a genuine
maximum rather than Mathlib's junk value on an unbounded set. -/

/-- For `x ≥ 0` the distance to the nearest integer never exceeds `x` itself. Proved from the
`min` characterisation, so it is pinned to Mathlib's `abs_sub_round_eq_min` and not to a
hand-chosen convention. -/
-- @category test
theorem nearestIntDist_le_self {x : ℝ} (hx : 0 ≤ x) : nearestIntDist x ≤ x := by
  have hfl : (0 : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hx
  have hfr : Int.fract x ≤ x := by
    have h : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
    rw [h]; linarith
  rw [nearestIntDist_eq_min]
  exact (min_le_left _ _).trans hfr

/-- **The step the packing argument turns on.** The source's condition is on `‖dist P Q‖`, which
on its face only keeps distances away from the integers. It nevertheless forces genuine
Euclidean separation: distinct points of an admissible configuration are at distance at least
`δ`. Without this the configurations could be arbitrarily crowded and `N` would be unbounded. -/
-- @category test
theorem dist_ge_of_isAdmissible {X δ : ℝ} {S : Finset Plane} (hS : IsAdmissible X δ S)
    {P Q : Plane} (hP : P ∈ S) (hQ : Q ∈ S) (hPQ : P ≠ Q) : δ ≤ dist P Q :=
  (hS.2 P hP Q hQ hPQ).trans (nearestIntDist_le_self dist_nonneg)

/-- **The packing bound.** For `δ > 0` there is a single `B` bounding the size of EVERY
admissible configuration in the disc of radius `X`. Proved by total boundedness of the closed
disc (it is compact in `EuclideanSpace ℝ (Fin 2)`): finitely many balls of radius `δ/2` cover
it, and by `dist_ge_of_isAdmissible` no two distinct admissible points fall in the same one. -/
-- @category test
theorem exists_bound_card_isAdmissible (X : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℕ, ∀ S : Finset Plane, IsAdmissible X δ S → S.card ≤ B := by
  obtain ⟨t, ht, hcov⟩ :=
    Metric.totallyBounded_iff.mp
      (isCompact_closedBall (0 : Plane) X).totallyBounded (δ / 2) (by linarith)
  refine ⟨ht.toFinset.card, fun S hS => ?_⟩
  have key : ∀ P : Plane, P ∈ S → ∃ y, y ∈ t ∧ dist P y < δ / 2 := by
    intro P hP
    have hball : P ∈ Metric.closedBall (0 : Plane) X := by
      simpa [Metric.mem_closedBall] using hS.1 P hP
    have hmem := hcov hball
    simpa [Set.mem_iUnion, Metric.mem_ball, exists_prop] using hmem
  choose! f hf hfd using key
  refine Finset.card_le_card_of_injOn f (fun P hP => ht.mem_toFinset.mpr (hf P hP)) ?_
  intro P hP Q hQ hfeq
  simp only [Finset.mem_coe] at hP hQ
  by_contra hne
  have h1 := hfd P hP
  have h2 := hfd Q hQ
  have hsep : δ ≤ dist P Q := dist_ge_of_isAdmissible hS hP hQ hne
  have htri : dist P Q ≤ dist P (f P) + dist (f Q) Q := by
    rw [hfeq]; exact dist_triangle _ _ _
  rw [dist_comm (f Q) Q] at htri
  linarith

/-- The set of achievable configuration sizes — the set `N` takes the `sSup` of. Introduced only
so the two lemmas below can be stated about it; `N_eq_sSup_admissibleCards` records that this is
literally `N`'s own set, by `rfl`, so nothing is quietly substituted. -/
def admissibleCards (X δ : ℝ) : Set ℕ :=
  {n : ℕ | ∃ S : Finset Plane, IsAdmissible X δ S ∧ S.card = n}

/-- `N` is the `sSup` of `admissibleCards`, definitionally. -/
-- @category test
theorem N_eq_sSup_admissibleCards (X δ : ℝ) : N X δ = sSup (admissibleCards X δ) := rfl

/-- The set is NONEMPTY (`S = ∅` gives `0`), the first of `sSup`'s two junk conditions. -/
-- @category test
theorem admissibleCards_nonempty (X δ : ℝ) : (admissibleCards X δ).Nonempty :=
  ⟨0, ∅, ⟨by simp, by simp⟩, by simp⟩

/-- **The hazard, closed.** For `δ > 0` the set is BOUNDED ABOVE, so `Nat.sSup` returns a real
supremum and not its junk value `0`.

⛔ `0 < δ` is genuinely needed: at `δ = 0` the admissibility condition is vacuous, so for
`X ≥ 0` arbitrarily large configurations exist and `N X 0 = 0` IS the junk value. Every theorem
in this file instantiates `δ > 0` (`1/10`, or `0 < δ < δ₀`), so none of them lands there. -/
-- @category test
theorem admissibleCards_bddAbove (X : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    BddAbove (admissibleCards X δ) := by
  obtain ⟨B, hB⟩ := exists_bound_card_isAdmissible X hδ
  exact ⟨B, by rintro n ⟨S, hS, rfl⟩; exact hB S hS⟩

/-- The payoff: an admissible configuration's size really is a lower bound for `N`. This is
`le_csSup`, and it is exactly the step that the missing boundedness proof used to block. -/
-- @category test
theorem card_le_N_of_isAdmissible {X δ : ℝ} (hδ : 0 < δ) {S : Finset Plane}
    (hS : IsAdmissible X δ S) : S.card ≤ N X δ := by
  rw [N_eq_sSup_admissibleCards]
  exact le_csSup (admissibleCards_bddAbove X hδ) ⟨S, hS, rfl⟩

/-- **The witness form now implies the `N` form.** Stated as an implication between two
`Prop`s so that it is PROVED rather than sorried: it asserts nothing about Graham's theorem, only
that `graham_lower_bound_witness`'s statement entails `graham_lower_bound`'s. Before
`admissibleCards_bddAbove`, this implication was unavailable, which is precisely why the
`_witness` variants were written. -/
-- @category test
theorem graham_witness_imp_bound
    (h : ∀ᶠ X : ℝ in atTop,
      ∃ S : Finset Plane, IsAdmissible X (1 / 10) S ∧ Real.log X / 10 < (S.card : ℝ)) :
    ∀ᶠ X : ℝ in atTop, Real.log X / 10 < (N X (1 / 10) : ℝ) := by
  filter_upwards [h] with X hX
  obtain ⟨S, hS, hcard⟩ := hX
  have hle : S.card ≤ N X (1 / 10) :=
    card_le_N_of_isAdmissible (by norm_num : (0 : ℝ) < 1 / 10) hS
  have hle' : ((S.card : ℝ)) ≤ (N X (1 / 10) : ℝ) := by exact_mod_cast hle
  linarith

end Erdos466

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos466.nearestIntDist_eq_min
#print axioms Erdos466.graham_lower_bound
#print axioms Erdos466.graham_lower_bound_witness
#print axioms Erdos466.sarkozy_lower_bound
#print axioms Erdos466.sarkozy_lower_bound_witness
#print axioms Erdos466.erdos_466_answer
#print axioms Erdos466.nearestIntDist_le_self
#print axioms Erdos466.dist_ge_of_isAdmissible
#print axioms Erdos466.exists_bound_card_isAdmissible
#print axioms Erdos466.N_eq_sSup_admissibleCards
#print axioms Erdos466.admissibleCards_nonempty
#print axioms Erdos466.admissibleCards_bddAbove
#print axioms Erdos466.card_le_N_of_isAdmissible
#print axioms Erdos466.graham_witness_imp_bound
