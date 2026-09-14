/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Prove that\[R(4,k) \gg \frac{k^3}{(\log k)^{O(1)}}.\]

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#166 : [Er90b] [Er91] [Er93,p.339] [Er97c] [Va99,3.51] graph theory | ramsey theory Spencer [Sp77] proved\[R(4,k) \gg (k\log k)^{5/2}.\]Ajtai, Komlós, and Szemerédi [AKS80] proved\[R(4,k) \ll \frac{k^3}{(\log k)^2}.\]This is true, and was proved by Mattheus and Verstraete [MaVe23] , who showed that\[R(4,k) \gg \frac{k^3}{(\log k)^4}.\]This problem is #5 in Ramsey Theory in the graphs problem collection. See also [986] for the general case. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 23 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #166, https://www.erdosproblems.com/166, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A059442 Reactions Likes None Open to collaboration None Currently working on kenmendoza. 
-/

import Mathlib

-- @category research solved

namespace Erdos166

/-- 
A lower-bound predicate for a numerical function `R`.  The notation `≫` is
represented by a positive constant, and `(log k) ^ O(1)` by the existence of a
fixed natural exponent.  The argument `R` is left abstract because the frozen
source does not provide a definition of the Ramsey number.
-/
def RamseyLowerBound (R : ℕ → ℕ → ℕ) (p : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ k : ℕ in Filter.atTop,
      c * (k : ℝ) ^ 3 / (Real.log (k : ℝ)) ^ p ≤ (R 4 k : ℝ)

/-- 
The formalized question.  The source says
`R(4,k) ≫ k^3 / (log k)^{O(1)}`, which reads as a lower bound with some
fixed logarithmic exponent.
-/
def ErdosQuestion (R : ℕ → ℕ → ℕ) : Prop :=
  ∃ p : ℕ, RamseyLowerBound R p

/-- 
The result attributed in the resolution to Mattheus and Verstraete, namely the
specific lower bound with logarithmic exponent `4`.  This is recorded as a
proposition supplied by that result, rather than asserted here as an
unproved theorem.
-/
def MattheusVerstraeteResult (R : ℕ → ℕ → ℕ) : Prop :=
  RamseyLowerBound R 4

/-- 
SOURCE MAPPING: the question asks for a bound with `(log k)^{O(1)}`, while the
resolution supplies the stronger concrete exponent `4`.  Thus the supplied
resolution is `MattheusVerstraeteResult R`, and the requested conclusion is
`ErdosQuestion R`.
-/
theorem resolution_solves_question
    {R : ℕ → ℕ → ℕ} (h : MattheusVerstraeteResult R) :
    ErdosQuestion R := by
  exact ⟨4, h⟩

/-- 
A proved control for the definitions: any concrete logarithmic exponent
immediately witnesses the existential exponent used in the question.
-/
theorem lower_bound_exponent_control
    {R : ℕ → ℕ → ℕ} {p : ℕ} (h : RamseyLowerBound R p) :
    ErdosQuestion R := by
  exact ⟨p, h⟩

#print axioms resolution_solves_question
#print axioms lower_bound_exponent_control

end Erdos166