/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
For any finite colouring of the integers is there a covering system all of whose moduli are monochromatic?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#8 : [Er80,p.95] [ErGr80,p.25] [Er96b] [Er97] [Er97e] number theory | covering systems Conjectured by Erdős and Graham, who also ask about a density-type version: for example, is\[\sum_{\substack{a\in A\\ a>N}}\frac{1}{a}\gg \log N\]a sufficient condition for $A$ to contain the moduli of a covering system? The answer (to both colouring and density versions) is no, due to the result of Hough [Ho15] on the minimum size of a modulus in a covering system - in particular one could colour all integers $<10^{18}$ different colours and all other integers a new colour. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (2) Proof claims (0) More information and links This page was last edited 05 April 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #8, https://www.erdosproblems.com/8, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes holyterror Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




-- @category research solved

import Mathlib
namespace ErdosProblem8

/-- A finite colouring of the integers with `k` colours. -/
def FiniteColouring (k : ℕ) : Type :=
  ℤ → Fin k

/-- A covering system consists of distinct moduli, each at least two, with one
residue assigned to each modulus, such that every integer belongs to one of
the resulting congruence classes. -/
def IsCoveringSystem (moduli : Finset ℕ) (residue : ℕ → ℤ) : Prop :=
  moduli.Nonempty ∧
    (∀ m ∈ moduli, 2 ≤ m) ∧
      (∀ z : ℤ, ∃ m ∈ moduli, (m : ℤ) ∣ z - residue m)

/-- The moduli of a covering system are monochromatic for a colouring `c` when
all modulus integers receive one common colour. -/
def MonochromaticModuli {k : ℕ} (c : FiniteColouring k)
    (moduli : Finset ℕ) : Prop :=
  moduli.Nonempty ∧ ∃ q : Fin k, ∀ m ∈ moduli, c (m : ℤ) = q

/-- The source question, read literally as asking whether every finite colouring
admits a covering system all of whose moduli are monochromatic. -/
def Question : Prop :=
  ∀ k : ℕ, ∀ c : FiniteColouring k,
    ∃ moduli : Finset ℕ, ∃ residue : ℕ → ℤ,
      IsCoveringSystem moduli residue ∧ MonochromaticModuli c moduli

/-- The negative answer recorded in the resolution node: some finite colouring
admits no covering system with monochromatic moduli. This proposition records
the known result without pretending that the deep Hough theorem is reproved
here. -/
def HoughResolution : Prop :=
  ∃ k : ℕ, ∃ c : FiniteColouring k,
    ¬ ∃ moduli : Finset ℕ, ∃ residue : ℕ → ℤ,
      IsCoveringSystem moduli residue ∧ MonochromaticModuli c moduli

/-- Logical control: the negative answer is exactly the existence of one
finite colouring for which no suitable covering system exists. -/
theorem question_negation_iff_resolution :
    HoughResolution ↔ ¬ Question := by
  classical
  simp [HoughResolution, Question]

/-- Proved control exercising the direction and quantifier structure of the
formalized question. -/
theorem not_question_iff_exists_bad_colouring :
    ¬ Question ↔
      ∃ k : ℕ, ∃ c : FiniteColouring k,
        ¬ ∃ moduli : Finset ℕ, ∃ residue : ℕ → ℤ,
          IsCoveringSystem moduli residue ∧ MonochromaticModuli c moduli := by
  classical
  simp [Question]

#print axioms question_negation_iff_resolution
#print axioms not_question_iff_exists_bad_colouring

end ErdosProblem8
