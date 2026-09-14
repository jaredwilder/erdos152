/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
A set of integers $A$ is Ramsey $r$-complete if, whenever $A$ is $r$-coloured, all sufficiently large integers can be written as a monochromatic sum of elements of $A$. Prove any non-trivial bounds about the growth rate of such an $A$ for $r>2$.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#55 : [Er95] number theory | ramsey theory A paper of Burr and Erdős [BuEr85] proves both upper and lower bounds for $r=2$, showing that there exists some $c>0$ such that it cannot be true that\[\lvert A\cap \{1,\ldots,N\}\rvert \leq c(\log N)^2\]for all large $N$, and also constructing a Ramsey $2$-complete $A$ such that for all large $N$\[\lvert A\cap \{1,\ldots,N\}\rvert \ll (\log N)^3.\]Burr has shown that the sequence of $k$th powers is Ramsey $r$-complete for every $r,k\geq 1$. Solved by Conlon, Fox, and Pham [CFP21] , who constructed for every $r\geq 2$ an $r$-Ramsey complete $A$ such that for all large $N$\[\lvert A\cap \{1,\ldots,N\}\rvert \ll r(\log N)^2,\]and showed that this is best possible, in that there exists some constant $c>0$ such that if $A\subset \mathbb{N}$ satisfies\[\lvert A\cap \{1,\ldots,N\}\rvert \leq cr(\log N)^2\]for all large $N$ then $A$ cannot be $r$-Ramsey complete. See also [54] and [843] . Additional thanks to : Mehtaab Sawhney Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #55, https://www.erdosproblems.com/55, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/
import Mathlib

-- @category research solved

namespace Erdos55

/-- A sum of elements of `A` is monochromatic for a colouring `colour` when it is
the sum of a nonempty finite list whose entries all lie in `A` and have one common colour. -/
def MonochromaticSum (A : Set ℕ) (r : ℕ) (colour : ℕ → Fin r) (n : ℕ) : Prop :=
  ∃ c : Fin r, ∃ s : List ℕ,
    s ≠ [] ∧
    (∀ a ∈ s, a ∈ A) ∧
    (∀ a ∈ s, colour a = c) ∧
    s.sum = n

/-- A set is Ramsey `r`-complete when every `r`-colouring represents every
sufficiently large natural number by a monochromatic nonempty sum of elements of the set. -/
def RamseyComplete (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ colour : ℕ → Fin r, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → MonochromaticSum A r colour n

/-- The number of positive elements of `A` not exceeding `N`. This is the
formal counterpart of the counting function in the source's growth statements. -/
noncomputable def CountingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 N).filter (fun n => n ∈ A)).card

/-- An eventual quadratic logarithmic upper bound with the factor `r`, using
natural logarithms and real-valued constants to formalize the source's `\ll` notation. -/
def QuadraticUpperBound (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (CountingFunction A n : ℝ) ≤ C * (r : ℝ) * (Nat.log 2 n : ℝ) ^ 2

/-- The upper-bound assertion recorded in the resolution: for every `r ≥ 2`
there is an `r`-Ramsey-complete set with quadratic logarithmic growth. -/
def CFPUpperBound (r : ℕ) : Prop :=
  ∃ A : Set ℕ, RamseyComplete A r ∧ QuadraticUpperBound A r

/-- The lower-bound assertion recorded in the resolution: for each `r ≥ 2`
there is a positive constant forcing every set below the corresponding
quadratic logarithmic bound to fail Ramsey completeness. -/
def CFPLowerBound (r : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ A : Set ℕ,
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (CountingFunction A n : ℝ) ≤ c * (r : ℝ) * (Nat.log 2 n : ℝ) ^ 2) →
      ¬ RamseyComplete A r

/-- A formalized version of the question, retaining its range `r > 2` and
expressing “non-trivial bounds” by the upper and lower assertions used in the resolution. -/
def Question : Prop :=
  ∀ r : ℕ, 2 < r → CFPUpperBound r ∧ CFPLowerBound r

/-- The settled statement attributed in the resolution to Conlon, Fox, and
Pham: the upper and lower bounds hold for every `r ≥ 2`. -/
def CFP21Theorem : Prop :=
  ∀ r : ℕ, 2 ≤ r → CFPUpperBound r ∧ CFPLowerBound r

/-- A Ramsey-completeness witness remains valid after increasing its threshold
by one. This proved control exercises the definition of eventual monochromatic
representation. -/
theorem RamseyComplete.succ_threshold
    {A : Set ℕ} {r : ℕ} (h : RamseyComplete A r) :
    ∀ colour : ℕ → Fin r, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      MonochromaticSum A r colour n := by
  intro colour
  obtain ⟨N, hN⟩ := h colour
  refine ⟨N + 1, ?_⟩
  intro n hn
  exact hN n (le_trans (Nat.le_succ N) hn)

#print axioms RamseyComplete.succ_threshold

end Erdos55