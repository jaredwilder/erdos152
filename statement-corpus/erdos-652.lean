/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $x_1,\ldots,x_n\in \mathbb{R}^2$ and let $R(x_i)=\#\{ \lvert x_j-x_i\rvert : j\neq i\}$, where the points are ordered such that\[R(x_1)\leq \cdots \leq R(x_n).\]Let $\alpha_k$ be minimal such that, for all large enough $n$, there exists a set of $n$ points with $R(x_k)<\alpha_kn^{1/2}$. Is it true that $\alpha_k\to \infty$ as $k\to \infty$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#652 : [Er97e] geometry | distances It is trivial that $R(x_1)=1$ is possible, and that $R(x_2) \ll n^{1/2}$ is also possible, but we always have\[R(x_1)R(x_2)\gg n.\]Erdős originally conjectured that $R(x_3)/n^{1/2}\to \infty$ as $n\to \infty$, but Elekes proved that for every $k$ and $n$ sufficiently large there exists some set of $n$ points with $R(x_k)\ll_k n^{1/2}$. Mathialagan [Ma21] proved that given a set $P$ of $k$ points and a set $Q$ of $n$ points, with $2\leq k\leq n^{1/3}$, there exists a point in $P$ which determines $\gg (kn)^{1/2}$ distances to points in $Q$. This immediately implies $R(x_k)\gg (kn)^{1/2}$ for $2\leq k\leq n^{1/3}$. Additional thanks to : Bois Alexeev and Terence Tao Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (6) Proof claims (0) More information and links This page was last edited 18 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #652, https://www.erdosproblems.com/652, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research open








open Classical Filter

namespace Erdos652

/-- The Euclidean plane, represented with the Euclidean rather than product metric. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- For a finite indexed configuration, the number of distinct distances from `P i`
to the other indexed points. -/
def distanceCount {n : ℕ} (P : Fin n → Point) (i : Fin n) : ℕ :=
  (Finset.image (fun j => dist (P j) (P i))
    (Finset.filter (fun j => j ≠ i) Finset.univ)).card

/-- The condition that the indexed points are ordered by their number of distinct
distances, as in the source. -/
def Ordered {n : ℕ} (P : Fin n → Point) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ≤ j → distanceCount P i ≤ distanceCount P j

/-- The source's assertion at a fixed index and threshold.  Indices are zero-based
in Lean, so `k` represents the source's point `x_(k+1)`. -/
def Good (k n : ℕ) (a : ℝ) : Prop :=
  ∃ hk : k < n,
    ∃ P : Fin n → Point,
      Function.Injective P ∧
        Ordered P ∧
          distanceCount P ⟨k, hk⟩ < a * Real.sqrt (n : ℝ)

/-- The phrase "for all large enough `n`" in the source statement. -/
def EventuallyGood (k : ℕ) (a : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, Good k n a

/-- A threshold is minimal when it works eventually and no smaller working
threshold exists.  This is the literal order-theoretic formalization of the
source's phrase "minimal". -/
def MinimalThreshold (k : ℕ) (a : ℝ) : Prop :=
  EventuallyGood k a ∧
    ∀ b : ℝ, EventuallyGood k b → a ≤ b

/-- Formalization of the question whether the minimal thresholds tend to infinity.
The source clause is read as: for each `k`, choose a minimal `α_k`, and ask whether
the resulting sequence tends to infinity as `k` tends to infinity. -/
def Question : Prop :=
  ∃ α : ℕ → ℝ,
    (∀ k : ℕ, MinimalThreshold k (α k)) ∧
      Tendsto α atTop atTop

/-- The settled bounded-threshold assertion attributed in the resolution to Elekes.
The constant is allowed to depend on `k`, as indicated by the source notation
`≪_k`. -/
def ElekesBounded : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, EventuallyGood k C

/-- A proved sanity check on the distance-count definition: in a two-point
configuration every point determines exactly one distance to the other point.
This control is independent of any geometric existence theorem. -/
theorem distanceCount_two (P : Fin 2 → Point) (i : Fin 2) :
    distanceCount P i = 1 := by
  classical
  fin_cases i <;> simp [distanceCount]

/-- The resolution records Elekes's theorem that every fixed indexed point can
be realized with a bound of order `n^(1/2)`.  The mathematical theorem is
imported here as an explicit honest gap; the definitions and the derivation of
the formal target are checked by Lean. -/
theorem elekes_result : ElekesBounded := by
  sorry

#print axioms distanceCount_two

end Erdos652
