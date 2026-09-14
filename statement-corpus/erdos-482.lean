/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Define a sequence by $a_1=1$ and\[a_{n+1}=\lfloor\sqrt{2}(a_n+1/2)\rfloor\]for $n\geq 1$. The difference $a_{2n+1}-2a_{2n-1}$ is the $n$th digit in the binary expansion of $\sqrt{2}$. Find similar results for $\theta=\sqrt{m}$, and other algebraic numbers.

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#482 : [ErGr80,p.96] number theory The result for $\sqrt{2}$ was obtained by Graham and Pollak [GrPo70] . The problem statement is open-ended, but presumably Erdős and Graham would have been satisfied with the wide-ranging generalisations of Stoll ( [St05] and [St06] ). Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 28 September 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #482, https://www.erdosproblems.com/482, accessed 2026-08-30 From the external database . You can help update this.) Formalised statement? No ( create one ) OEIS A004539 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising gotrevor Previous Next
-/


import Mathlib
open Classical

-- @category research open








open Classical Filter

namespace Erdos482

/-- The sequence from the question, with the auxiliary value `a₀ = 0` used only
to make the definition total.  The displayed recurrence is the literal
floor recurrence from the source. -/
noncomputable def seq : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      ⌊Real.sqrt 2 * ((seq (n + 1) : ℝ) + (1 / 2 : ℝ))⌋₊

/-- The auxiliary zeroth value of the formalized sequence. -/
theorem seq_zero : seq 0 = 0 := by
  rfl

/-- The initial condition `a₁ = 1` from the source. -/
theorem seq_one : seq 1 = 1 := by
  rfl

/-- The recursive clause for every index at least two. -/
theorem seq_recurrence (n : ℕ) :
    seq (n + 2) =
      ⌊Real.sqrt 2 * ((seq (n + 1) : ℝ) + (1 / 2 : ℝ))⌋₊ := by
  rfl

/-- The `k`th binary digit convention used here is
`⌊2^(k-1) θ⌋ mod 2` for positive `k`; the zeroth value is auxiliary. -/
noncomputable def binaryDigit (θ : ℝ) (k : ℕ) : ℕ :=
  if k = 0 then 0
  else (⌊(2 : ℝ) ^ (k - 1) * θ⌋₊) % 2

/-- A proved control showing that the auxiliary binary-digit definition is
not an unrestricted or constantly chosen value at index zero. -/
theorem binaryDigit_zero (θ : ℝ) : binaryDigit θ 0 = 0 := by
  simp [binaryDigit]

/-- The literal digit-extraction assertion for the known `sqrt 2` result.
The source's phrase “the nth digit” is represented by `binaryDigit (sqrt 2) n`.
This is recorded as a literature claim; the cited source reports the result,
but this artifact does not reproduce its proof. -/
theorem sqrt_two_digit_result :
    ∀ n : ℕ, 1 ≤ n →
      seq (2 * n + 1) - 2 * seq (2 * n - 1) =
        binaryDigit (Real.sqrt 2) n := by
  sorry

/-- Algebraicity over the rationals for a real number, expressed by the
existence of a nonzero rational polynomial having that number as a root. -/
def IsAlgebraicReal (θ : ℝ) : Prop :=
  ∃ p : Polynomial ℚ,
    p ≠ 0 ∧ Polynomial.eval₂ (algebraMap ℚ ℝ) θ p = 0

/-- The property sought by the open-ended question: a sequence starts at one,
satisfies the same floor recurrence with parameter `θ`, and its indicated
differences recover the binary digits of `θ`. -/
def ExtractsBinaryDigits (θ : ℝ) (b : ℕ → ℕ) : Prop :=
  b 1 = 1 ∧
    (∀ n : ℕ, 1 ≤ n →
      b (n + 1) =
        ⌊θ * ((b n : ℝ) + (1 / 2 : ℝ))⌋₊) ∧
    (∀ n : ℕ, 1 ≤ n →
      b (2 * n + 1) - 2 * b (2 * n - 1) =
        binaryDigit θ n)

/-- Formal version of the open-ended request for analogous digit-extraction
results for square roots and for other algebraic real numbers.  It is stated
as a proposition rather than as a theorem, since the source records this
generalization problem as open. -/
def GeneralizationQuestion : Prop :=
  (∀ m : ℕ, 2 ≤ m →
    ∃ b : ℕ → ℕ, ExtractsBinaryDigits (Real.sqrt m) b) ∧
  (∀ θ : ℝ, IsAlgebraicReal θ →
    ∃ b : ℕ → ℕ, ExtractsBinaryDigits θ b)

#print axioms seq_zero
#print axioms seq_one
#print axioms seq_recurrence

end Erdos482
