/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $g(n)$ be the maximal size of $A\subseteq \{1,\ldots,n\}$ such that the products $\prod_{n\in S}n$ are distinct for all $S\subseteq A$. Is it true that\[g(n) \leq \pi(n)+\pi(n^{1/2})+o\left(\frac{x^{1/2}}{\log n}\right)?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#795 : [Er65] [Er69] [Er70b] [Er80,p.102] number theory Erdős proved [Er66] \[g(n) \leq \pi(n)+O\left(\frac{x^{1/2}}{\log n}\right).\]This upper bound would be essentially best possible, since one could take $A$ to be all primes and squares of primes. This was solved by Raghavan [Ra25] , who proved that\[g(n) \leq \pi(n)+\pi(n^{1/2})+O(n^{5/12+o(1)}),\]and also that\[g(n) \geq \pi(n)+\pi(n^{1/2})+\pi(n^{1/3})/3-O(1).\]In [Er80] Erdős made the stronger conjecture that\[g(n)=\pi(n)+\pi(n^{1/2})+\pi(n^{1/4})+\pi(n^{1/7})+\cdots,\]where $\pi(n^{1/k})$ occurs if and only if $F(k)>F(k-1)$, where $F(k)$ is the maximal size of a dissociated set in $\{1,\ldots,k\}$ (see [1] ). This is disproved by the lower bound of Raghavan. See also [786] . Additional thanks to : Rishika Agrawal and Ryan Alweiss Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 06 April 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. The recommended citation format is: T. F. Bloom, Erdős Problem #795, https://www.erdosproblems.com/795, accessed 2026-08-30
-/







import Mathlib
open Classical
open Filter
open scoped BigOperators

-- @category research solved






open Classical Filter

namespace Erdos795

/-- The product of the elements of a finite set of natural numbers. -/
def subsetProduct (S : Finset ℕ) : ℕ :=
  ∏ x ∈ S, x

/-- A finite set is dissociated when its subset products are pairwise distinct. -/
def IsDissociated (A : Finset ℕ) : Prop :=
  ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A →
    subsetProduct S = subsetProduct T → S = T

/-- The subsets of `{1, ..., n}` which satisfy the dissociated-subset-product condition. -/
def dissociatedSubsets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter IsDissociated

/-- The maximal cardinality in the definition of the Erdős function `g`. -/
noncomputable def g (n : ℕ) : ℕ :=
  (dissociatedSubsets n).sup Finset.card

/-- The number of primes in the interval `{1, ..., n}`. -/
def primeCount (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).filter Nat.Prime |>.card

/--
The original question, with the displayed `x` interpreted as `n`, and with
`π(n^(1/2))` represented by `primeCount (Nat.sqrt n)`.  The little-oh term is
formalized by an eventual real-valued error function.
-/
def OriginalQuestion : Prop :=
  ∃ h : ℕ → ℝ,
    IsLittleO atTop h
      (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 2) / Real.log n) ∧
    ∀ᶠ n : ℕ in atTop,
      (g n : ℝ) ≤ primeCount n + primeCount (Nat.sqrt n) + h n

/--
An explicit interpretation of Raghavan's recorded upper bound
`g(n) ≤ π(n) + π(n^(1/2)) + O(n^(5/12+o(1)))`: for every positive
epsilon, the excess is eventually bounded by a constant times
`n^(5/12 + epsilon)`.
-/
def RaghavanUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop,
        (g n : ℝ) ≤ primeCount n + primeCount (Nat.sqrt n) +
          C * (n : ℝ) ^ ((5 : ℝ) / 12 + ε)

/-- The defining function has the expected pinned value at the empty endpoint. -/
theorem g_zero_control : g 0 = 0 := by
  simp [g, dissociatedSubsets, IsDissociated, subsetProduct]

/-- There are no primes in the empty initial interval. -/
theorem primeCount_zero_control : primeCount 0 = 0 := by
  simp [primeCount]

/--
Raghavan's solved upper bound, recorded using the explicit asymptotic
interpretation in `RaghavanUpperBound`.  The mathematical proof of this
literature result remains to be formalized.
-/
theorem raghavan_upper_bound : RaghavanUpperBound := by
  sorry

#print axioms g_zero_control
#print axioms primeCount_zero_control

end Erdos795
