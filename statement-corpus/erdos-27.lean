/-
SOURCE (frozen), node `n000-question`, VERBATIM:
An $\epsilon$-almost covering system is a set of congruences $a_i\pmod{n_i}$ for distinct moduli $n_1<\cdots<n_k$ such that the density of those integers which satisfy none of them is $\leq \epsilon$. Is there a constant $C>1$ such that for every $\epsilon>0$ and $N\geq 1$ there is an $\epsilon$-almost covering system with $N\leq n_1<\cdots < n_k\leq CN$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#27 : [Er95,p.4] number theory | covering systems By a simple averaging argument the set of moduli $[m_1,m_2]\cap \mathbb{N}$ has a choice of residue classes which form an $\epsilon(m_1,m_2)$-almost covering system with\[\epsilon(m_1,m_2)=\prod_{m_1\leq m\leq m_2}(1-1/m).\]A $0$-covering system is just a covering system, and so by Hough [Ho15] these only exist for $n_1<10^{18}$ (now $<616000$ thanks to [BBMST22] ). The answer is no, as proved by Filaseta, Ford, Konyagin, Pomerance, and Yu [FFKPY07] , who (among other results) prove that if\[1< C \leq N^{\frac{\log\log\log N}{4\log\log N}}\]then, for any $N\leq n_1<\cdots< n_k\leq CN$, the density of integers not covered for any fixed choice of residue classes is at least\[(1-o(1))\prod_{i}(1-1/n_i)\](and this density is achieved for some choice of residue classes as above). Additional thanks to : Mehtaab Sawhney and Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (2) Proof claims (0) More information and links This page was last edited 16 July 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #27, https://www.erdosproblems.com/27, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes holyterror Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

import Mathlib
open Classical

-- @category research solved

namespace Erdos27

/-- A congruence is represented by its residue and modulus. -/
def Congruence := ℕ × ℕ

/-- An integer satisfies a congruence when it has the prescribed residue modulo its modulus. -/
def Satisfies (c : Congruence) (x : ℕ) : Prop :=
  x % c.2 = c.1 % c.2

/-- The integers not covered by a finite indexed family of congruences. -/
def Uncovered (k : ℕ) (c : Fin k → Congruence) (x : ℕ) : Prop :=
  ∀ i, ¬ Satisfies (c i) x

/-- The number of integers below `x` satisfying a predicate. -/
noncomputable def DensityCount (P : ℕ → Prop) (x : ℕ) : ℕ :=
  (Finset.filter P (Finset.range x)).card

/-- A predicate has asymptotic density `d`, expressed by convergence of its initial-segment densities. -/
def HasDensity (P : ℕ → Prop) (d : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ M : ℕ, ∀ x : ℕ, M ≤ x →
      |(DensityCount P x : ℝ) / (x : ℝ) - d| < δ

/-- The moduli of a family are strictly increasing and lie in the prescribed interval. -/
def OrderedSystem (N : ℕ) (C : ℝ) (k : ℕ) (c : Fin k → Congruence) : Prop :=
  (∀ i, N ≤ (c i).2) ∧
  (∀ i, ((c i).2 : ℝ) ≤ C * (N : ℝ)) ∧
  (∀ i j, i.val < j.val → (c i).2 < (c j).2)

/-- An epsilon-almost covering system with moduli between `N` and `C N`. -/
def AlmostCovering (ε : ℝ) (N : ℕ) (C : ℝ) : Prop :=
  ∃ k : ℕ, ∃ c : Fin k → Congruence,
    OrderedSystem N C k c ∧
      ∃ d : ℝ, HasDensity (Uncovered k c) d ∧ d ≤ ε

/-- The question asks whether one constant works for every positive error and every positive lower modulus. -/
def Question : Prop :=
  ∃ C : ℝ, 1 < C ∧
    ∀ ε : ℝ, 0 < ε →
      ∀ N : ℕ, 1 ≤ N →
        AlmostCovering ε N C

/-- The recorded resolution of Erdős problem 27: the answer to the question is negative. -/
def KnownResolution : Prop :=
  ¬ Question

/-- The empty family leaves every integer uncovered. -/
theorem emptySystem_hasDensity :
    HasDensity
      (fun x : ℕ => ∀ i : Fin 0, ¬ Satisfies (Fin.elim0 i) x)
      1 := by
  classical
  intro δ hδ
  refine ⟨1, by norm_num, ?_⟩
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le (by decide) hx
  have hxreal : (x : ℝ) ≠ 0 := by
    positivity
  simpa [DensityCount, hxreal] using hδ

#print axioms emptySystem_hasDensity

end Erdos27