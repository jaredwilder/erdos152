/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
What is the largest possible subset $A\subseteq\{1,\ldots,N\}$ which contains $N$ such that $\mathrm{gcd}(a,b)>1$ for all $a\neq b\in A$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#534 : [Er73] [Er80,p.113] number theory | intersecting family A problem of Erdős and Graham (in [Er73] it was stated with $(a,b)=1$ instead but this is clearly a typo). They conjecture that this maximum is either $N/p$ (where $p$ is the smallest prime factor of $N$) or it is the number of integers $\{2t: t\leq N/2\textrm{ and }(2t,N)> 1\}$. Ahlswede and Khachatrian [AhKh96] observe that it is 'easy' to find a counterexample to this conjecture, which they informed Erdős about in 1992. Erdős then gave a refined conjecture, that if $N=q_1^{k_1}\cdots q_r^{k_r}$ (where $q_1<\cdots <q_r$ are distinct primes) then the maximum is achieved by, for some $1\leq j\leq r$, those integers in $[1,N]$ which are a multiple of at least one of
\[\{2q_1,\ldots,2q_j,q_1\cdots q_j\}.\]
This conjecture was proved by Ahlswede and Khachatrian [AhKh96] .
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos534

/-- A finite subset of `[1,N]` containing `N` whose distinct members have gcd greater than one. -/
def Admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    N ∈ A ∧
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.gcd a b > 1

/-- The set of cardinalities of admissible families for `N`. -/
def FeasibleCardinalities (N : ℕ) : Set ℕ :=
  {k | ∃ A : Finset ℕ, Admissible N A ∧ A.card = k}

/-- The extremal cardinality, using `sSup` on the natural numbers.  The
nonemptiness and boundedness controls below ensure that this `sSup` is not
being used at an empty or unbounded set; without them, `sSup` would return
Lean's default junk value. -/
noncomputable def ExtremalCardinality (N : ℕ) : ℕ :=
  sSup (FeasibleCardinalities N)

/-- The singleton family consisting of `N` is admissible whenever `N` is positive. -/
theorem singleton_admissible {N : ℕ} (hN : 1 ≤ N) :
    Admissible N ({N} : Finset ℕ) := by
  refine ⟨?_, by simp, ?_⟩
  · intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    simp [hN]
  · intro a ha b hb hab
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    exact False.elim (hab rfl)

/-- The feasible cardinalities are nonempty for positive `N`; this is the
nonemptiness control required for the `sSup` definition. -/
theorem feasible_cardinalities_nonempty {N : ℕ} (hN : 1 ≤ N) :
    (FeasibleCardinalities N).Nonempty := by
  refine ⟨1, ?_⟩
  refine ⟨{N}, singleton_admissible hN, by simp⟩

/-- The feasible cardinalities are bounded above by `N + 1`; this is the
boundedness control required for the `sSup` definition. -/
theorem feasible_cardinalities_bddAbove (N : ℕ) :
    BddAbove (FeasibleCardinalities N) := by
  refine ⟨N + 1, ?_⟩
  rintro k ⟨A, hA, rfl⟩
  have hsub : A ⊆ Finset.range (N + 1) := by
    intro x hx
    have hx' := hA.1 hx
    simp only [Finset.mem_Icc] at hx'
    simp only [Finset.mem_range]
    omega
  have hc := Finset.card_le_card hsub
  simpa using hc

/-- The extremal cardinality is at least one for positive `N`, exercising
both the family definition and the controlled `sSup`. -/
theorem one_le_extremalCardinality {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ ExtremalCardinality N := by
  apply le_csSup (feasible_cardinalities_bddAbove N)
  exact ⟨{N}, singleton_admissible hN, by simp⟩

/-- The original question, formalized as attainment of the extremal
cardinality by an admissible finite family. -/
def Question (N : ℕ) : Prop :=
  ∃ A : Finset ℕ, Admissible N A ∧ A.card = ExtremalCardinality N

/-- The finite set of integers in `[1,N]` divisible by at least one of the
numbers `2q` for `q` among the first `j` entries of `q`, or by the product of
those first `j` entries. -/
def RefinedFamily (N : ℕ) (q : List ℕ) (j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter
    (fun a =>
      (∃ p ∈ q.take j, 2 * p ∣ a) ∨
        (q.take j).prod ∣ a)

/-- A list-based encoding of a factorization
`N = q₁ᵏ¹ ⋯ qᵣᵏʳ` with increasing distinct prime factors and positive
exponents. -/
def PrimeFactorization (N : ℕ) (q ks : List ℕ) : Prop :=
  q.length = ks.length ∧
    q.Pairwise (· < ·) ∧
    (∀ p ∈ q, Nat.Prime p) ∧
    (∀ k ∈ ks, 1 ≤ k) ∧
    N = (q.zipWith (fun p k => p ^ k) ks).prod

/-- Erdős's refined Ahlswede--Khachatrian conclusion: for a factorization of
`N`, the maximum is attained by one of the displayed families.  The
mathematical proof of this theorem is the external result cited in the
source and remains an explicit proof gap here. -/
theorem ahlswede_khachatrian_refined (N : ℕ) (hN : 2 ≤ N) :
    ∃ (q ks : List ℕ) (j : ℕ),
      PrimeFactorization N q ks ∧
      1 ≤ j ∧
      j ≤ q.length ∧
      ExtremalCardinality N = (RefinedFamily N q j).card := by
  sorry Erdos534
