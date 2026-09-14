/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Is it true that, in any finite colouring of the integers, there must be two integers $x\neq y$ of the same colour such that $x+y$ is a square? What about a $k$th power?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#439 : [ErSa77] [Er80,p.105] [Er80c] [ErGr80] [Er80c] number theory | ramsey theory A question of Roth, Erdős, Sárközy, and Sós [ESS89] (according to some reports, although in [Er80c] Erdős claims this arose in a conversation with Silverman in 1977). Erdős, Sárközy, and Sós [ESS89] proved this for $2$ or $3$ colours. In other words, if $G$ is the infinite graph on $\mathbb{N}$ where we connect $m,n$ by an edge if and only if $n+m$ is a square, then is the chromatic number of $G$ equal to $\aleph_0$? This is true, as proved by Khalfalah and Szemerédi [KhSz06] , who in fact prove the general result with $x+y=z^2$ replaced by $x+y=f(z)$ for any non-constant $f(z)\in \mathbb{Z}[z]$ such that $2\mid f(z)$ for some $z\in \mathbb{Z}$. See also [438] . Additional thanks to : Deepak Bal Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 07 April 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #439, https://www.erdosproblems.com/439, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Can be formalisable JoshuaB Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos439

/-- A finite colouring of the integers with `k` colours, represented by an
integer-valued colour assigned to every integer. -/
def FiniteColouring (k : ℕ) := ℤ → Fin k

/-- `HasPowerPair c r` says that the colouring `c` contains distinct integers
of the same colour whose sum is an `r`th power of an integer. -/
def HasPowerPair {k : ℕ} (c : FiniteColouring k) (r : ℕ) : Prop :=
  ∃ x y : ℤ, x ≠ y ∧ c x = c y ∧ ∃ z : ℤ, x + y = z ^ r

/-- The square case of the question: every finite colouring of the integers
has a monochromatic distinct pair whose sum is a square. -/
def QuestionSquare : Prop :=
  ∀ k : ℕ, 0 < k → ∀ c : FiniteColouring k, HasPowerPair c 2

/-- The `r`th-power version of the question, for every positive exponent `r`. -/
def QuestionKthPower : Prop :=
  ∀ r : ℕ, 0 < r → ∀ k : ℕ, 0 < k →
    ∀ c : FiniteColouring k, HasPowerPair c r

/-- A proved sanity check: with one colour, the distinct integers `1` and `3`
have the same colour and their sum is the square `2²`. -/
theorem one_color_control (c : FiniteColouring 1) :
    HasPowerPair c 2 := by
  refine ⟨1, 3, by norm_num, Subsingleton.elim _ _, ?_⟩
  exact ⟨2, by norm_num⟩

/-- Khalfalah and Szemerédi's theorem, specialized to monomials: for every
positive exponent and every finite colouring, a monochromatic distinct pair
has sum equal to an integer power. The proof of this literature result remains
an explicit formalization gap. -/
theorem kth_power_result (r : ℕ) (hr : 0 < r) :
    ∀ k : ℕ, 0 < k → ∀ c : FiniteColouring k, HasPowerPair c r := by
  sorry

/-- The settled square case of the source question, derived by specializing
the assumed general polynomial result to the polynomial `z ↦ z²`. -/
theorem square_result : QuestionSquare := by
  intro k hk c
  exact kth_power_result 2 (by norm_num) k hk c

#print axioms square_result

end Erdos439
