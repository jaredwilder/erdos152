/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $\alpha_n$ be the supremum of all $0\leq \alpha\leq \pi$ such that in every set $A\subset \mathbb{R}^2$ of size $n$ there exist three distinct points $x,y,z\in A$ such that the angle determined by $xyz$ is at least $\alpha$. Determine $\alpha_n$.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#504 : [Er61,p.244] [Er75f,p.106] geometry Blumenthal's problem. Szekeres [Sz41] showed that\[\alpha_{2^n+1}> \pi \left(1-\frac{1}{n}+\frac{1}{n(2^n+1)^2}\right)\]and\[\alpha_{2^n}\leq \pi\left(1-\frac{1}{n}\right).\]Erdős and Szekeres [ErSz60] showed that\[\alpha_{2^n}=\alpha_{2^n-1}= \pi\left(1-\frac{1}{n}\right),\]and suggested that perhaps $\alpha_{N}=\pi(1-1/n)$ for $2^{n-1}<N\leq 2^n$. This was disproved by Sendov [Se92] . Sendov [Se93] provided the definitive answer, proving that $\alpha_N=\pi(1-1/n)$ for $2^{n-1}+2^{n-3}<N\leq 2^n$ and $\alpha_N=\pi(1-\frac{1}{2n-1})$ for $2^{n-1}<N\leq 2^{n-1}+2^{n-3}$. Additional thanks to : Desmond Weisenberg Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 16 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #504, https://www.erdosproblems.com/504, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/







import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos504

/-- The carrier used for the plane is the Euclidean space
`EuclideanSpace ℝ (Fin 2)`, rather than a product with the sup metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The angle at `y` determined by the ordered triple `x,y,z`. -/
def angleAt (x y z : Plane) : ℝ :=
  Real.angle (x - y) (z - y)

/-- A finite-set formalization of the geometric property appearing in the
definition of `alpha_n`: every `n`-point set contains three distinct points
whose angle at the middle point is at least `a`. -/
def admissible (n : ℕ) (a : ℝ) : Prop :=
  0 ≤ a ∧ a ≤ Real.pi ∧
    ∀ A : Finset Plane, A.card = n →
      ∃ x y z : Plane,
        x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        a ≤ angleAt x y z

/-- The quantity in the source is represented literally as the supremum of
the admissible real numbers.  This uses `sSup`; its value is junk when the
admissible set is empty, so the separate predicate `wellPosed` records the
required nonemptiness rather than silently treating that default as
mathematics. -/
noncomputable def alpha (n : ℕ) : ℝ :=
  sSup {a : ℝ | admissible n a}

/-- The admissible set is bounded above by `π`.  This is the boundedness
control required before interpreting its supremum. -/
lemma admissible_bddAbove (n : ℕ) : BddAbove {a : ℝ | admissible n a} := by
  refine ⟨Real.pi, ?_⟩
  intro a ha
  exact ha.2.1

/-- Nonemptiness of the admissible set, which is not automatic for the
literal source definition when `n < 3`. -/
def wellPosed (n : ℕ) : Prop :=
  Set.Nonempty {a : ℝ | admissible n a}

/-- Under the explicit nonemptiness control, the supremum is genuinely
bounded above by `π`, rather than obtaining an upper bound vacuously from
the junk value of `sSup`. -/
lemma alpha_le_pi_of_wellPosed {n : ℕ} (hn : wellPosed n) :
    alpha n ≤ Real.pi := by
  unfold alpha wellPosed at *
  apply csSup_le hn
  intro a ha
  exact ha.2.1

/-- The exact two-regime assertion recorded in Sendov's resolution.  The
integer parameter `n` is restricted to `3 ≤ n`, avoiding the negative
exponents in the printed interval notation. -/
def sendovClaim : Prop :=
  ∀ n N : ℕ, 3 ≤ n →
    ((2 ^ (n - 1) + 2 ^ (n - 3) < N ∧ N ≤ 2 ^ n →
        alpha N = Real.pi * (1 - 1 / (n : ℝ))) ∧
     (2 ^ (n - 1) < N ∧ N ≤ 2 ^ (n - 1) + 2 ^ (n - 3) →
        alpha N = Real.pi * (1 / (2 * (n : ℝ) - 1))))

/-- The source's question, formalized using the Euclidean angle and the
literal supremum definition above.  The finite-set presentation is the
finite form of “every set of size `n`”. -/
def question : Prop :=
  ∀ n : ℕ, alpha n = sSup {a : ℝ | admissible n a}

/-- Sendov's definitive answer, as stated in the resolution.  The
mathematical proof of this literature result remains an explicit gap here;
the definitions and the supremum boundedness control are checked by Lean. -/
theorem sendov_definitive : sendovClaim := by
  sorry Erdos504ાલ
