/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $d\geq 2$ and $n\geq 2$. Let $f_d(n)$ be maximal such that there exists some set of $n$ points $A\subseteq \mathbb{R}^d$, with diameter $1$, in which the distance 1 occurs between $f_d(n)$ many pairs of points in $A$. Estimate $f_d(n)$.

NODE n001-resolution (resolution), VERBATIM:
#223 : [Er46b] [Er57] [Er75f,p.102] geometry | distances In [Er46b] Erdős says this was a conjecture of Vázsonyi. Hopf and Pannwitz [HoPa34] proved $f_2(n)=n$ (with an elegant simple proof described by Erdős in [Er46b] ). Grünbaum [Gr56] , Heppes [He56] , and Strasziewicz [St57] independently showed that $f_3(n)=2n-2$. Erdős [Er60b] proved that, for $d\geq 4$, $f_d(n)=(\frac{p-1}{2p}+o(1))n^2$ where $p=\lfloor d/2\rfloor$. Swanepoel [Sw09] gave, for all $d\geq 4$, an exact description of $f_d(n)$ for all $n$ sufficiently large depending on $d$, and also gave the extremal configurations. See also [132] , and [1084] for the analogous problem with minimal distance $1$. Additional thanks to : Mark Sellke and Desmond Weisenberg Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 28 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #223, https://www.erdosproblems.com/223, accessed 2026-08-30 From the external database . You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next <!-
-/






import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos223

/-- A configuration of `n` distinct points in `d`-dimensional Euclidean space has
diameter exactly one when all pairwise distances are at most one and some pair
has distance exactly one. -/
def HasUnitDiameter (d n : ℕ) (A : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  Function.Injective A ∧
    (∀ i j, dist (A i) (A j) ≤ 1) ∧
    (∃ i j, dist (A i) (A j) = 1)

/-- The number of unordered pairs at distance one in a point configuration.
The inequality `p.1 < p.2` ensures that each unordered pair is counted once. -/
def unitPairCount (d n : ℕ) (A : Fin n → EuclideanSpace ℝ (Fin d)) : ℕ :=
  (Finset.univ.filter
    (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ dist (A p.1) (A p.2) = (1 : ℝ))).card

/-- The set of attainable numbers of unit-distance pairs among admissible
configurations. -/
def attainableValues (d n : ℕ) : Set ℕ :=
  {k | ∃ A : Fin n → EuclideanSpace ℝ (Fin d),
    HasUnitDiameter d n A ∧ unitPairCount d n A = k}

/-- The literal formalization of the source's maximal value.  Since this uses
` sSup`, the required nonemptiness and boundedness facts are recorded separately:
without them `Nat.sSup` would return its junk default on an empty or unbounded set. -/
noncomputable def f (d n : ℕ) : ℕ :=
  sSup (attainableValues d n)

/-- Every unit-pair count is bounded by the number of ordered pairs, hence by
`n * n`.  This is a proved anti-vacuity control for the counting definition. -/
theorem unitPairCount_le_square (d n : ℕ)
    (A : Fin n → EuclideanSpace ℝ (Fin d)) :
    unitPairCount d n A ≤ n * n := by
  unfold unitPairCount
  have hsub :
      (Finset.univ.filter
        (fun p : Fin n × Fin n =>
          p.1 < p.2 ∧ dist (A p.1) (A p.2) = (1 : ℝ))) ⊆
        (Finset.univ : Finset (Fin n × Fin n)) :=
    Finset.filter_subset _ _
  calc
    (Finset.univ.filter
        (fun p : Fin n × Fin n =>
          p.1 < p.2 ∧ dist (A p.1) (A p.2) = (1 : ℝ))).card
        ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
      Finset.card_le_card hsub
    _ = n * n := by simp [Fintype.card_prod]

/-- The attainable-value set is bounded above.  This proves the boundedness
needed to interpret the `sSup` in `f`; the remaining issue is nonemptiness. -/
theorem attainableValues_bddAbove (d n : ℕ) :
    BddAbove (attainableValues d n) := by
  refine ⟨n * n, ?_⟩
  rintro k ⟨A, hA, rfl⟩
  exact unitPairCount_le_square d n A

/-- For `d ≥ 2` and `n ≥ 2`, admissible configurations exist.  The omitted
proof is the elementary construction of `n` distinct points on a unit-diameter
configuration; this named gap is kept separate so that the `sSup` definition
does not silently rely on its junk value. -/
theorem attainableValues_nonempty {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ≤ n) :
    (attainableValues d n).Nonempty := by
  sorry

/-- Consequently, in the source's range `d,n ≥ 2`, the supremum defining `f`
is backed by both nonemptiness and boundedness rather than by `Nat.sSup`'s
default value. -/
theorem f_is_well_controlled {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ≤ n) :
    (attainableValues d n).Nonempty ∧ BddAbove (attainableValues d n) :=
  ⟨attainableValues_nonempty hd hn, attainableValues_bddAbove d n⟩

/-- An epsilon formulation of the asymptotic estimate
`f_d(n) = ((p - 1) / (2p) + o(1)) n²`, where `p = floor (d/2)`.
The coercions to `ℝ` make the asymptotic statement an ordinary two-sided
eventual estimate. -/
def QuadraticAsymptoticEstimate (d : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 ≤ n →
      (((((d / 2 : ℕ) : ℝ) - 1) / (2 * ((d / 2 : ℕ) : ℝ)) - ε) * (n : ℝ)^2
          ≤ (f d n : ℝ)) ∧
      ((f d n : ℝ) ≤
        (((((d / 2 : ℕ) : ℝ) - 1) / (2 * ((d / 2 : ℕ) : ℝ)) + ε) * (n : ℝ)^2))

/-- The settled planar formula recorded in the resolution.  Its proof is not
reconstructed here; it is the named literature result of Hopf and Pannwitz. -/
theorem planar_formula :
    ∀ n : ℕ, 2 ≤ n → f 2 n = n := by
  sorry

/-- The settled three-dimensional formula recorded in the resolution.  Its
proof is not reconstructed here; it is the named result independently proved
by Grünbaum, Heppes, and Strasziewicz. -/
theorem three_dimensional_formula :
    ∀ n : ℕ, 2 ≤ n → f 3 n = 2 * n - 2 := by
  sorry

/-- The settled high-dimensional estimate recorded in the resolution. -/
theorem high_dimensional_estimate :
    ∀ d : ℕ, 4 ≤ d → QuadraticAsymptoticEstimate d := by
  sorry

/-- Combined formal statement of the resolution: exact formulas in dimensions
two and three, and the quadratic asymptotic estimate in every dimension at
least four. -/
theorem resolution :
    (∀ n : ℕ, 2 ≤ n → f 2 n = n) ∧
    (∀ n : ℕ, 2 ≤ n → f 3 n = 2 * n - 2) ∧
    (∀ d : ℕ, 4 ≤ d → QuadraticAsymptoticEstimate d) := by
  sorry

#print axioms unitPairCount_le_square
#print axioms attainableValues_bddAbove
#print axioms f_is_well_controlled

end Erdos223
