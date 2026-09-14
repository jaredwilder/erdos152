/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $c,\epsilon>0$ and $n$ be sufficiently large. If $A\subset \mathbb{N}$ has $\lvert A\rvert=n$ and $G$ is any graph on $A$ with at least $n^{1+c}$ edges then\[\max(\lvert A+_GA\rvert,\lvert A\cdot_G A\rvert) \geq \lvert A\rvert^{1+c-\epsilon},\]where\[A+_GA = \{ a+b : (a,b)\in G\}\]and similarly for $A\cdot_GA$.
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#808 : [Er77c] [ErSz83] [Er91] [Er97] additive combinatorics | graph theory A problem often attributed to Erdős and Szemerédi, which strengthens the conjecture [52] , although it appears in [Er77c] without attribution to Szemerédi. This strong conjecture was disproved by Alon, Ruzsa, and Solymosi [ARS20] , who constructed (for arbitrarily large $n$) a set of integers $A$ with $\lvert A\rvert=n$ and a graph $G$ with $\gg n^{5/3-o(1)}$ many edges such that\[\max(\lvert A+_GA\rvert,\lvert A\cdot_G A\rvert) \ll \lvert A\rvert^{4/3+o(1)}.\]Alon, Ruzsa, and Solymosi do prove, however, that if $A$ has size $n$ and $G$ has $m$ edges then\[\max(\lvert A+_GA\rvert,\lvert A\cdot_G A\rvert) \gg m^{3/2}n^{-7/4}.\] Additional thanks to : Noga Alon Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #808, https://www.erdosproblems.com/808, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos808

/-- A finite encoding of a set of natural numbers together with its graph edges. -/
structure FiniteInstance where
  A : Finset ℕ
  E : Finset (ℕ × ℕ)

/-- The restricted sumset determined by the listed graph edges. -/
def graphSum (E : Finset (ℕ × ℕ)) : Finset ℕ :=
  E.image (fun p => p.1 + p.2)

/-- The restricted product set determined by the listed graph edges. -/
def graphProd (E : Finset (ℕ × ℕ)) : Finset ℕ :=
  E.image (fun p => p.1 * p.2)

/-- The larger of the restricted sumset and product-set cardinalities. -/
def graphOutput (E : Finset (ℕ × ℕ)) : ℕ :=
  max (graphSum E).card (graphProd E).card

/-- A bounded, decidable finite-instance test exercising the large-edge and large-output conditions. -/
def finiteOutputProperty (I : FiniteInstance) : Prop :=
  I.E ⊆ I.A.product I.A ∧
    I.E.card ≥ I.A.card + 1 ∧
    graphOutput I.E ≥ I.A.card + 1

/-- POSITIVE WITNESS: the complete directed graph on `{1, 2}` satisfies the finite test. -/
theorem finiteOutputProperty_witness_pos :
    finiteOutputProperty
      { A := ({1, 2} : Finset ℕ)
        E := ({(1, 1), (1, 2), (2, 1), (2, 2)} : Finset (ℕ × ℕ))} := by
  decide

/-- NEGATIVE WITNESS: deleting exactly the edge `(2, 2)` preserves the edge-count condition but breaks the output condition. -/
theorem finiteOutputProperty_witness_neg :
    ¬ finiteOutputProperty
      { A := ({1, 2} : Finset ℕ)
        E := ({(1, 1), (1, 2), (2, 1)} : Finset (ℕ × ℕ))} := by
  decide

/-- The source conjecture, with a graph represented by a finite set of ordered pairs on `A`.
The phrase “sufficiently large” is read as the existence of a threshold `N`, and the
cardinalities are compared with real powers. -/
def strongClaim : Prop :=
  ∀ c ε : ℝ, 0 < c → 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : Finset ℕ, A.card = n →
        ∀ E : Finset (ℕ × ℕ), E ⊆ A.product A →
          (E.card : ℝ) ≥ Real.rpow (n : ℝ) (1 + c) →
          (graphOutput E : ℝ) ≥ Real.rpow (n : ℝ) (1 + c - ε)

/-- The resolution recorded by the source: the strong conjecture is false, by the
counterexamples of Alon, Ruzsa, and Solymosi. The literature-level counterexample
construction is not reproved here. -/
theorem strongClaim_disproved : ¬ strongClaim := by
  sorry Erdos808
