/-!
SOURCE (frozen), node `n000-question`, VERBATIM:
Is there an explicit construction of a set $A\subseteq \mathbb{N}$ such that $A+A=\mathbb{N}$ but $1_A\ast 1_A(n)=o(n^\epsilon)$ for every $\epsilon>0$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#29 : [ErGr80,p.48] [Er89d] [Er95] [Er97c] number theory | additive basis The existence of such a set was asked by Sidon to Erdős in 1932. Erdős (eventually) proved the existence of such a set using probabilistic methods. This problem asks for a constructive solution. An explicit construction was given by Jain, Pham, Sawhney, and Zakharov [JPSZ24] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 28 December 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #29, https://www.erdosproblems.com/29, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes holyterror Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

-- @category research solved

import Mathlib

namespace ErdosProblem29

/-- A set of natural numbers is an additive basis when every natural number is
the sum of two of its elements. -/
def AdditiveBasis (A : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ a ∈ A, ∃ b ∈ A, a + b = n

/-- The number of representations of `n` as a sum of two elements of `A`,
counting the first summand. -/
noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.filter
    (fun a => a ∈ A ∧ ∃ b, b ∈ A ∧ a + b = n)
    (Finset.range (n + 1))).card

/-- The bounded representation predicate used to relate representation counts
to the additive-basis condition. -/
def BoundedRepresentation (A : Set ℕ) (n : ℕ) : Prop :=
  ∃ a ≤ n, a ∈ A ∧ ∃ b, b ∈ A ∧ a + b = n

/-- A positive representation count is equivalent to the existence of a
bounded representation. -/
theorem representationCount_pos_iff (A : Set ℕ) (n : ℕ) :
    0 < representationCount A n ↔ BoundedRepresentation A n := by
  classical
  simp [representationCount, BoundedRepresentation, Nat.lt_succ_iff]

/-- An additive basis is exactly a set for which every natural number has a
positive representation count. -/
theorem additiveBasis_iff_representationCount_pos (A : Set ℕ) :
    AdditiveBasis A ↔ ∀ n : ℕ, 0 < representationCount A n := by
  constructor
  · intro h n
    rw [representationCount_pos_iff]
    rcases h n with ⟨a, ha, b, hb, hab⟩
    refine ⟨a, ?_, ha, b, hb, hab⟩
    omega
  · intro h n
    rw [representationCount_pos_iff] at h
    rcases h n with ⟨a, _, ha, b, hb, hab⟩
    exact ⟨a, ha, b, hb, hab⟩

/-- The representation function is subpolynomial when it is
`o(n^ε)` for every positive real exponent. -/
def SubpolynomialRepresentations (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Filter.Tendsto
      (fun n : ℕ =>
        (representationCount A n : ℝ) / (n : ℝ) ^ ε)
      Filter.atTop (nhds 0)

/-- The formalized question asks for an additive basis whose representation
function is subpolynomial. -/
def Question : Prop :=
  ∃ A : Set ℕ, AdditiveBasis A ∧ SubpolynomialRepresentations A

/-- The existence claim recorded in the resolution node, separated from the
wording of the original question. -/
def KnownResolution : Prop :=
  ∃ A : Set ℕ, AdditiveBasis A ∧ SubpolynomialRepresentations A

/-- With the explicit construction abstracted to the existence of the
corresponding set, the formalized question and the recorded resolution have
the same proposition. -/
theorem question_iff_knownResolution :
    Question ↔ KnownResolution :=
  Iff.rfl

#print axioms representationCount_pos_iff
#print axioms additiveBasis_iff_representationCount_pos
#print axioms question_iff_knownResolution

end ErdosProblem29