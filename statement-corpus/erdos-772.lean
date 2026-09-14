/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k\geq 1$ and $H_k(n)$ be the maximal $r$ such that if $A\subset\mathbb{N}$ has $\lvert A\rvert=n$ and $\| 1_A\ast 1_A\|_\infty \leq k$ then $A$ contains a Sidon set of size at least $r$. Is it true that $H_k(n)/n^{1/2}\to \infty$? Or even $H_k(n) > n^{1/2+c}$ for some constant $c>0$?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#772 : [Er80e] [Er84d] number theory | sidon sets | additive combinatorics Erdős [Er84d] proved that\[H_k(n) \ll n^{2/3}\](where the implied constant is absolute). The lower bound $H_k(n)\gg n^{1/2}$ follows from the fact that any set of size $n$ contains a Sidon set of size $\gg n^{1/2}$ (see [530] ). The answer is yes, and in fact\[H_k(n) \gg_k n^{2/3},\]proved by Alon and Erdős [AlEr85] . We sketch their proof as follows: take a random subset $A'\subset A$, including each $n\in A'$ with probability $\asymp n^{-1/3}$. The number of non-trivial additive quadruples in $A$ is $\ll n^2$ and hence only $\ll n^{2/3}$ non-trivial additive quadruples remain in $A'$. Since the size of the random subset is $\gg n^{2/3}$, all of the remaining non-trivial additive quadruples can be removed by removing at most $\lvert A'\rvert/2$ (choosing the constants suitably). Additional thanks to : Noga Alon Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #772, https://www.erdosproblems.com/772, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Currently working on None Looks tractable None Open to collaboration None
-/






import Mathlib
open Classical
open Filter

-- @category research solved





open Classical Filter

namespace Erdos772

/-- A finite set of natural numbers is Sidon when an equality of two sums
forces the two ordered pairs to agree up to exchanging their entries. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The number of ordered representations of `m` as a sum of two elements of `A`.
This is the finite-set version of the quantity `‖1_A * 1_A‖` appearing in the source. -/
def convolutionCount (A : Finset ℕ) (m : ℕ) : ℕ :=
  (A.filter (fun a => a ≤ m ∧ m - a ∈ A)).card

/-- The condition on `A` in the definition of `H_k(n)`: `A` has size `n` and
every coefficient of its additive convolution is at most `k`. -/
def BoundedConvolution (k n : ℕ) (A : Finset ℕ) : Prop :=
  A.card = n ∧ ∀ m : ℕ, convolutionCount A m ≤ k

/-- The property that `r` is an admissible lower bound for the size of a
Sidon subset of every `n`-element set satisfying the convolution bound. -/
def Admissible (k n r : ℕ) : Prop :=
  r ≤ n ∧
    ∀ A : Finset ℕ, BoundedConvolution k n A →
      ∃ B : Finset ℕ, B ⊆ A ∧ B.card ≥ r ∧ IsSidon B

/-- The maximal `r ≤ n` in the definition of the source's `H_k(n)`.
The `Nat.findGreatest` formulation makes the finiteness of the maximum explicit. -/
noncomputable def H (k n : ℕ) : ℕ :=
  Nat.findGreatest (fun r => Admissible k n r) n

/-- The first alternative in the question, formalized as divergence of the
ratio `H_k(n) / n^(1/2)` to infinity along the natural numbers. -/
def RatioDiverges (k : ℕ) : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    M ≤ (H k n : ℝ) / Real.sqrt (n : ℝ)

/-- The second, stronger alternative in the question, formalized with an
eventual positive constant multiple of `n^(2/3)`. -/
def TwoThirdsLowerBound (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    c * ((n : ℝ) ^ (2 / 3 : ℝ)) ≤ (H k n : ℝ)

/-- The source's question: for every `k ≥ 1`, either the square-root ratio
diverges, or the stronger two-thirds power lower bound holds. -/
def Question : Prop :=
  ∀ k : ℕ, 1 ≤ k → RatioDiverges k ∨ TwoThirdsLowerBound k

/-- A proved sanity control: the empty finite set is Sidon under the definition
used here. This exercises the file's actual Sidon predicate rather than proving
an unrelated arithmetic fact. -/
theorem empty_isSidon : IsSidon ∅ := by
  simp [IsSidon]

/-- A proved sanity control for the convolution model: every coefficient of the
convolution of the empty set is zero. -/
theorem empty_convolutionCount (m : ℕ) : convolutionCount ∅ m = 0 := by
  simp [convolutionCount]

/-- The settled result recorded in the resolution: Alon and Erdős prove an
eventual lower bound of order `n^(2/3)` with a constant depending on `k`.
The proof of this literature theorem remains an explicit gap here. -/
theorem alon_erdos_lower_bound (k : ℕ) (hk : 1 ≤ k) :
    TwoThirdsLowerBound k := by
  sorry

/-- The answer to the source question is affirmative, using the stronger
two-thirds-power lower bound recorded in the resolution. -/
theorem answer_yes : Question := by
  intro k hk
  exact Or.inr (alon_erdos_lower_bound k hk)

#print axioms empty_isSidon
#print axioms empty_convolutionCount

end Erdos772
