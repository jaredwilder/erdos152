/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
We say that $A\subset \mathbb{N}$ is an essential component if $d_s(A+B)>d_s(B)$ for every $B\subset \mathbb{N}$ with $0<d_s(B)<1$ where $d_s$ is the Schnirelmann density . Can a lacunary set $A\subset\mathbb{N}$ be an essential component?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#37 : [Er56,p.136] [Er61,p.229] [Er73,p.135] [ErGr80,p.49] number theory | additive combinatorics The answer is no by Ruzsa [Ru87] , who proved that if $A$ is an essential component then there exists some constant $c>0$ such that $\lvert A\cap \{1,\ldots,N\}\rvert \geq (\log N)^{1+c}$ for all large $N$. Furthermore, Ruzsa proves that this is best possible, in that for any $c>0$ there exists an essential component $A$ for which $\lvert A\cap \{1,\ldots,N\}\rvert \leq (\log N)^{1+c}$ for all large $N$. See also [1146] for whether $\{2^m3^n\}$ is an essential component. Additional thanks to : Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. Comments (2) Proof claims (0) More information and links This page was last edited 23 January 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #37, https://www.erdosproblems.com/37, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes holyterror Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

import Mathlib

-- @category research solved

namespace ErdosProblem37

/-- The number of elements of `A` in the interval `{1, ..., n}`. -/
def countingFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun k => k ∈ A ∧ k ≠ 0) |>.card

/-- The proportion of the first `n` positive integers which belong to `A`. -/
def initialDensity (A : Set ℕ) (n : ℕ) : ℝ :=
  (countingFunction A n : ℝ) / n

/-- The Schnirelmann density of a set of natural numbers, using the literal
formalization of the source's notation `d_s`. -/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  sInf (Set.range (initialDensity A))

/-- The sumset `A + B` of two subsets of the natural numbers. -/
def sumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a, a ∈ A ∧ ∃ b, b ∈ B ∧ a + b = n}

/-- `EssentialComponent A` means that `A` increases Schnirelmann density
after addition to every set of intermediate density. -/
def EssentialComponent (A : Set ℕ) : Prop :=
  ∀ B : Set ℕ,
    0 < schnirelmannDensity B →
      schnirelmannDensity B < 1 →
        schnirelmannDensity (sumset A B) > schnirelmannDensity B

/-- We use the following explicit counting formulation as the formal reading
of “lacunary”: the counting function is eventually bounded by a constant
multiple of `log N`. This choice is recorded because the frozen source does
not define the word `lacunary`. -/
def Lacunary (A : Set ℕ) : Prop :=
  ∃ C N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    countingFunction A N ≤ C * (Nat.log 2 N + 1)

/-- The lower-growth conclusion attributed in the resolution to Ruzsa. -/
def RuzsaLowerBound (A : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (countingFunction A N : ℝ) ≥
      Real.rpow (Nat.log 2 N : ℝ) (1 + c)

/-- The analytic incompatibility between the Ruzsa lower bound and the
chosen logarithmic counting bound for lacunary sets. -/
def LacunaryExcludesRuzsaBound : Prop :=
  ∀ A : Set ℕ, RuzsaLowerBound A → ¬ Lacunary A

/-- A proved control showing that the orientation of `sumset` is as intended:
the first set supplies the first summand and the second set supplies the
second summand. -/
theorem zero_mem_sumset {A B : Set ℕ} (hA : 0 ∈ A) (hB : 0 ∈ B) :
    0 ∈ sumset A B := by
  refine ⟨0, hA, 0, hB, ?_⟩
  simp

/-- The settled result is recorded as a derivation from the two mathematical
inputs described in the resolution: Ruzsa's lower bound and the fact that
that bound excludes lacunarity. The source question is read word by word as
asking whether there exists `A` which is both lacunary and an essential
component; the answer is no. -/
theorem no_lacunary_essential_component
    (hRuzsa :
      ∀ A : Set ℕ, EssentialComponent A → RuzsaLowerBound A)
    (hExclude : LacunaryExcludesRuzsaBound) :
    ¬ ∃ A : Set ℕ, Lacunary A ∧ EssentialComponent A := by
  rintro ⟨A, hLacunary, hEssential⟩
  exact hExclude A (hRuzsa A hEssential) hLacunary

#print axioms zero_mem_sumset
#print axioms no_lacunary_essential_component

end ErdosProblem37