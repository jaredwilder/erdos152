/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Does every connected set in $\mathbb{R}^n$ contain a connected subset which is not a point and not homeomorphic to the original set? If $n\geq 2$ does every connected set in $\mathbb{R}^n$ contain more than $2^{\aleph_0}$ many connected subsets?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#910 : [Er82e] topology Asked by Erdős in the 1940s, who thought the answer to both questions is yes. The answer to both is in fact no, as shown by Rudin [Ru58] (conditional on the continuum hypothesis). Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #910, https://www.erdosproblems.com/910, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos910

/-- A subset of a topological space is not a point when it contains two distinct points. -/
def NonPoint {X : Type*} (s : Set X) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, x ≠ y

/-- `HasAlternativeConnectedSubset s` says that `s` contains a connected,
non-point subset which is not homeomorphic to `s` itself. -/
def HasAlternativeConnectedSubset {X : Type*} [TopologicalSpace X]
    (s : Set X) : Prop :=
  ∃ t : Set X,
    t ⊆ s ∧ IsConnected t ∧ NonPoint t ∧ ¬ Nonempty (Homeomorph t s)

/-- The first question from Erdős Problem 910, formalized using the genuine
Euclidean space `EuclideanSpace ℝ (Fin n)`. -/
def QuestionOne : Prop :=
  ∀ n : ℕ, ∀ s : Set (EuclideanSpace ℝ (Fin n)),
    IsConnected s → HasAlternativeConnectedSubset s

/-- The second question from Erdős Problem 910: for every dimension at least
two, every connected set has more than continuum many connected subsets. -/
def QuestionTwo : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ s : Set (EuclideanSpace ℝ (Fin n)),
      IsConnected s →
        Cardinal.mk
            {t : Set (EuclideanSpace ℝ (Fin n)) // IsConnected t ∧ t ⊆ s} >
          Cardinal.continuum

/-- A bounded, decidable finite control for the non-point condition. -/
def FiniteNonPoint (s : Finset (Fin 3)) : Prop :=
  2 ≤ s.card

/-- POSITIVE WITNESS: a finite set satisfying the non-point condition. -/
theorem FiniteNonPoint_witness_pos :
    FiniteNonPoint ({0, 1} : Finset (Fin 3)) := by
  decide

/-- NEGATIVE WITNESS: a near-miss obtained by removing one point from the
positive witness. -/
theorem FiniteNonPoint_witness_neg :
    ¬ FiniteNonPoint ({0} : Finset (Fin 3)) := by
  decide

/-- A concrete topological control: the whole Euclidean space is connected. -/
theorem euclidean_univ_connected (n : ℕ) :
    IsConnected (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := by
  simpa using
    (isConnected_univ : IsConnected (Set.univ : Set (EuclideanSpace ℝ (Fin n))))

/-- A concrete topological control: every singleton is connected. -/
theorem singleton_connected {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    IsConnected ({x} : Set (EuclideanSpace ℝ (Fin n))) := by
  simpa using (isConnected_singleton x)

/-- The resolution is recorded conditionally on the continuum hypothesis.
The source says that Rudin showed both questions have negative answers under
that hypothesis; the proof of Rudin's result is not supplied here. -/
theorem rudin_resolution
    (hCH : Cardinal.continuum = Cardinal.aleph 1) :
    ¬ QuestionOne ∧ ¬ QuestionTwo := by
  sorry

#print axioms FiniteNonPoint_witness_pos
#print axioms FiniteNonPoint_witness_neg
#print axioms euclidean_univ_connected
#print axioms singleton_connected

end Erdos910
