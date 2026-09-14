/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $A\subseteq \mathbb{N}$. Can there exist some constant $c>0$ such that\[\sum_{n\leq N} 1_A\ast 1_A\ast 1_A(n) = cN+O(1)?\]

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#764 : [Er65b] [Er70c] number theory | additive combinatorics The case of $1_A\ast 1_A(n)$ is the subject of [763] . The answer is no, proved in a strong form by Vaughan [Va72] , who showed that in fact\[\sum_{n\leq N} 1_A\ast 1_A\ast 1_A(n) = cN+o\left(\frac{N^{1/4}}{(\log N)^{1/2}}\right)\]is impossible. Vaughan proves a more general result that applies to any $h$-fold convolution, with different main terms permitted. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #764, https://www.erdosproblems.com/764, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos764

/-- The indicator of a set of natural numbers, viewed as a natural-valued function. -/
noncomputable def oneA (A : Set ℕ) : ℕ → ℕ :=
  fun n => if n ∈ A then 1 else 0

/-- The additive convolution of two natural-valued functions on `ℕ`, summed over
all decompositions `n = k + (n-k)`. -/
noncomputable def convolution (f g : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), f k * g (n - k)

/-- The triple additive convolution appearing in the source question. -/
noncomputable def tripleConvolution (A : Set ℕ) (n : ℕ) : ℕ :=
  convolution (convolution (oneA A) (oneA A)) (oneA A) n

/-- The partial sum of the triple convolution through `N`, with the natural
count viewed as a real number. -/
noncomputable def tripleSum (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), (tripleConvolution A n : ℝ)

/-- A literal formalization of the question's assertion that the partial sums
are `c N + O(1)`: the error is bounded uniformly over all natural `N`. -/
def TripleLinearQuestion : Prop :=
  ∃ A : Set ℕ, ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, |tripleSum A N - c * (N : ℝ)| ≤ C

/-- Sanity control: the triple convolution of the empty set vanishes at every
argument, and hence its partial sums vanish. -/
theorem empty_triple_sum (N : ℕ) :
    tripleSum (∅ : Set ℕ) N = 0 := by
  simp [tripleSum, tripleConvolution, convolution, oneA]

/-- Sanity control: the triple convolution for the singleton set `{0}` has
value one at zero. -/
theorem singleton_triple_at_zero :
    tripleConvolution ({0} : Set ℕ) 0 = 1 := by
  simp [tripleConvolution, convolution, oneA]

/-- The source asks whether there exist `A`, a positive constant `c`, and a
uniformly bounded error giving `tripleSum A N = cN + O(1)`.  The resolution
records that the answer is no.  This theorem is the formalized core result;
its mathematical proof by Vaughan's theorem remains to be supplied. -/
theorem vaughan_no_constant :
    ¬ TripleLinearQuestion := by
  sorry Erdos764
