/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $A\subset \mathbb{R}^2$ be a set of size $n$ and let $\{d_1<\ldots<d_k\}$ be the set of distinct distances determined by $A$. Let $f(d)$ be the number of times the distance $d$ is determined. Is it true that\[f(d_1)f(d_k) \leq (\tfrac{9}{8}+o(1))n^2?\]
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#957 : [ErPa90] geometry | distances A question of Erdős and Pach [ErPa90] , who write that an 'easy' unpublished construction of Makai shows that this would be the best possible, and that it is 'not difficult' to prove\[f(d_1)+f(d_k) \leq 3n -c\sqrt{n}+o(\sqrt{n})\]for some $c>0$, and ask what the best possible value of $c$ is. A stronger version of this problem (which implies the inequality in the problem statement) is that\[f(d_1)\leq 3n-2m+o(\sqrt{n}),\]where $m$ is the number of vertices of the convex hull of $A$. The odd regular polygon shows that it is possible for $f(d_i)\geq n$ for all $i$. The original problem was solved by Dumitrescu [Du19] , who proved that\[f(d_1)f(d_k)\leq \frac{9}{8}n^2+O(n).\]See also [132] and [756] . Additional thanks to : Adrian Dumitrescu Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #957, https://www.erdosproblems.com/957, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos957

/-- A finite planar configuration, represented using the genuine Euclidean plane
`EuclideanSpace ℝ (Fin 2)` rather than a product equipped with the sup metric. -/
abbrev PointConfig (n : ℕ) := Fin n → EuclideanSpace ℝ (Fin 2)

/-- The number of unordered pairs of points in a configuration whose distance is `d`.
The filter uses `i < j`, so each pair is counted once. -/
noncomputable def distanceMultiplicity {n : ℕ} (A : PointConfig n) (d : ℝ) : ℕ :=
  ((Finset.univ.product (Finset.univ : Finset (Fin n))).filter
    (fun p => p.1 < p.2 ∧ dist (A p.1) (A p.2) = d)).card

/-- A finite arithmetic control for the normalized inequality
`8ab ≤ 9n²`, together with the natural counting bounds `a,b ≤ n`.
This is a decidable finite-instance proxy for the two endpoint multiplicities. -/
def FiniteProfileBound (n a b : ℕ) : Prop :=
  a ≤ n ∧ b ≤ n ∧ 8 * a * b ≤ 9 * n * n

/-- POSITIVE WITNESS: the concrete finite profile `(n,a,b) = (2,1,1)` satisfies
all counting bounds and the normalized inequality. -/
theorem finiteProfileBound_witness_pos : FiniteProfileBound 2 1 1 = True := by
  decide

/-- NEGATIVE WITNESS: `(2,2,1)` is a near miss of the positive profile: it
breaks exactly the first counting bound `a ≤ n`, while the second counting
bound and normalized inequality remain true. -/
theorem finiteProfileBound_witness_neg : ¬ FiniteProfileBound 2 2 1 := by
  decide

#print axioms finiteProfileBound_witness_pos
#print axioms finiteProfileBound_witness_neg

/-- Dumitrescu's resolved theorem in an exact eventual form.  The hypotheses
say that `d₁` and `dₖ` are respectively the least and greatest distances
among all distinct pairs, and that both endpoint distances occur.  The
`C * n` term is the formal counterpart of the source's `O(n)` term.

SOURCE-TO-FORMAL MAPPING: the source's `f(d₁)` and `f(dₖ)` are represented by
`distanceMultiplicity A d₁` and `distanceMultiplicity A dₖ`; the Euclidean
distance is the metric on `EuclideanSpace ℝ (Fin 2)`.  The source records this
result as solved by Dumitrescu [Du19].  The remaining gap is the imported
mathematical proof of this geometric estimate. -/
theorem dumitrescu_distance_product_bound :
    ∃ C N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (A : PointConfig n) (d₁ dₖ : ℝ),
        (∀ i j : Fin n, i ≠ j → 0 < dist (A i) (A j)) →
        (∀ i j : Fin n, i < j →
          d₁ ≤ dist (A i) (A j) ∧ dist (A i) (A j) ≤ dₖ) →
        (∃ i j : Fin n, i < j ∧ dist (A i) (A j) = d₁) →
        (∃ i j : Fin n, i < j ∧ dist (A i) (A j) = dₖ) →
        distanceMultiplicity A d₁ * distanceMultiplicity A dₖ
          ≤ (9 * n * n) / 8 + C * n := by
  sorry Erdos957
