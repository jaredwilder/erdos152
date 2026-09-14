/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Is there some function $f(n)\to \infty$ as $n\to\infty$ such that there exist $n$ distinct points on the surface of a two-dimensional sphere with at least $f(n)n$ many pairs of points whose distances are the same?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#605 : [Er85] geometry | distances See also [90] . This was solved by Erdős, Hickerson, and Pach [EHP89] . For $D>1$ and $n\geq 2$ let $u_D(n)$ be such that there is a set of $n$ points on the sphere in $\mathbb{R}^3$ with radius $D$ such that there are $u_D(n)$ many pairs which are distance $1$ apart (so that this problem asked for $u_D(n)\geq f(n)n$ for some $D$). Erdős, Hickerson, and Pach [EHP89] proved that $u_{\sqrt{2}}(n)\asymp n^{4/3}$ and $u_D(n)\gg n\log^*n$ for all $D>1$ and $n\geq 2$ (where $\log^*$ is the iterated logarithm function). This lower bound was improved by Swanepoel and Valtr [SwVa04] to $u_D(n) \gg n\sqrt{\log n}$. The best upper bound for general $D$ is $u_D(n)\ll n^{4/3}$. Additional thanks to : Dmitrii Zakharov Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #605, https://www.erdosproblems.com/605, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/






import Mathlib
open Classical
open Filter

-- @category research solved





open Classical Filter

namespace Erdos605

/-- Points on the ambient Euclidean three-space, whose norm spheres are
the two-dimensional spheres occurring in the source. -/
abbrev Point := EuclideanSpace ℝ (Fin 3)

/-- A finite list of points lies on the sphere of radius `D` centered at the
origin. -/
def OnSphere (D : ℝ) {n : ℕ} (p : Fin n → Point) : Prop :=
  ∀ i, ‖p i‖ = D

/-- The number of unordered pairs of distinct indices whose corresponding
points have mutual distance `d`. -/
noncomputable def pairCount {n : ℕ} (p : Fin n → Point) (d : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun ij => ij.1 < ij.2 ∧ dist (p ij.1) (p ij.2) = d)).card

/-- The assertion that `n` distinct points on the sphere of radius `D`
determine at least `f(n) * n` pairs with one common distance. -/
def HasManyEqualDistances (D : ℝ) (f : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ p : Fin n → Point, ∃ d : ℝ,
    Function.Injective p ∧
    OnSphere D p ∧
    (pairCount p d : ℝ) ≥ (f n : ℝ) * (n : ℝ)

/-- A proved sanity control: at zero points there are no index pairs.
This deliberately checks the pair-counting definition at its degenerate
endpoint; the substantive source question separately requires `n ≥ 2`. -/
theorem pairCount_empty (d : ℝ) :
    pairCount (fun i : Fin 0 => Fin.elim0 i) d = 0 := by
  classical
  simp [pairCount]

#print axioms pairCount_empty

/-- Formalization of the solved assertion in node `n000-question`.

The source asks for a function tending to infinity and a sphere on which,
for every `n ≥ 2`, there are `n` distinct points with at least `f(n) * n`
equal-distance pairs. The resolution states that this is solved, in fact
with the stronger lower bound `u_D(n) ≫ n * sqrt(log n)` for every `D > 1`.

The remaining gap is the formal proof of the geometric existence theorem
from the cited literature; the statement below records that result honestly
with `sorry`. -/
theorem erdos605 :
    ∃ D : ℝ, D > 1 ∧
      ∃ f : ℕ → ℕ,
        Tendsto f atTop atTop ∧
        ∀ n : ℕ, n ≥ 2 → HasManyEqualDistances D f n := by
  sorry Erdos605
