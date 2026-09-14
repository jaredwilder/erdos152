/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Are all large integers the sum of at most three powerful numbers (i.e. if $p\mid n$ then $p^2\mid n$)?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#941 : [Er76d] [Ob1] number theory | powerful This was given in 1986 in the Oberwolfach problem book as a problem of Erdős and Ivić. It was proved by Heath-Brown [He88] . See [1107] for the generalisation to $r$-powerful numbers with $r\geq 3$, and also [940] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 03 November 2025. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #941, https://www.erdosproblems.com/941, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A056828 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/



import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos941

/-- A natural number is powerful when every prime divisor occurs with exponent at
least two. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

/-- POSITIVE WITNESS: one is powerful. -/
theorem powerful_witness_pos : Powerful 1 := by
  intro p hp hdiv
  have hpone : p = 1 := Nat.dvd_one.mp hdiv
  subst p
  norm_num at hp

/-- NEGATIVE WITNESS: three is a near-miss, since its prime divisor three does
not occur twice. -/
theorem powerful_witness_neg : ¬ Powerful 3 := by
  intro h
  have h' := h 3 (by norm_num) (by norm_num)
  norm_num at h'

/-- A sum of at most three powerful numbers, allowing zero summands. -/
def IsSumOfAtMostThree (n : ℕ) : Prop :=
  ∃ a b c : ℕ,
    n = a + b + c ∧ Powerful a ∧ Powerful b ∧ Powerful c

/-- POSITIVE WITNESS: one is the sum of three powerful numbers, namely
`1 + 0 + 0`. -/
theorem isSum_witness_pos : IsSumOfAtMostThree 1 := by
  refine ⟨1, 0, 0, by norm_num, powerful_witness_pos, ?_, ?_⟩
  · intro p hp hdiv
    exact dvd_zero p
  · intro p hp hdiv
    exact dvd_zero p

/-- NEGATIVE WITNESS: seven is a near-miss: it cannot be expressed as a sum
of three powerful numbers. -/
theorem isSum_witness_neg : ¬ IsSumOfAtMostThree 7 := by
  have np2 : ¬ Powerful 2 := by
    intro h
    have h' := h 2 (by norm_num) (by norm_num)
    norm_num at h'
  have np3 : ¬ Powerful 3 := powerful_witness_neg
  have np5 : ¬ Powerful 5 := by
    intro h
    have h' := h 5 (by norm_num) (by norm_num)
    norm_num at h'
  have np6 : ¬ Powerful 6 := by
    intro h
    have h' := h 2 (by norm_num) (by norm_num)
    norm_num at h'
  have np7 : ¬ Powerful 7 := by
    intro h
    have h' := h 7 (by norm_num) (by norm_num)
    norm_num at h'
  have small :
      ∀ x : ℕ, x ≤ 7 → Powerful x → x = 0 ∨ x = 1 ∨ x = 4 := by
    intro x hx hp
    interval_cases x <;> simp_all
  rintro ⟨a, b, c, habc, ha, hb, hc⟩
  have ha' := small a (by omega) ha
  have hb' := small b (by omega) hb
  have hc' := small c (by omega) hc
  rcases ha' with rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl <;>
      rcases hc' with rfl | rfl | rfl <;>
        norm_num at habc

/-- The bounded powerful predicate used for finite computational controls. -/
def PowerfulFinite (n bound : ℕ) : Prop :=
  ∀ p : Fin (bound + 1), p.1.Prime → p.1 ∣ n → p.1 ^ 2 ∣ n

/-- A bounded finite-instance version of being a sum of at most three powerful
numbers. -/
def IsSumFinite (n bound : ℕ) : Prop :=
  ∃ a b c : Fin (bound + 1),
    n = a.1 + b.1 + c.1 ∧
      PowerfulFinite a.1 bound ∧
      PowerfulFinite b.1 bound ∧
      PowerfulFinite c.1 bound

/-- A decidable finite truncation of the assertion that all integers from `N`
onward are sums of at most three powerful numbers. -/
def QuestionFinite (N bound : ℕ) : Bool :=
  decide (∀ n : Fin (bound + 1), N ≤ n.1 → IsSumFinite n.1 bound)

/-- POSITIVE FINITE WITNESS: in the range through one, every integer from zero
onward has the required bounded representation. -/
theorem questionFinite_witness_pos : QuestionFinite 0 1 = true := by
  decide

/-- NEGATIVE FINITE WITNESS: the near-miss bound through seven fails at seven,
which is not a sum of three powerful numbers. -/
theorem questionFinite_witness_neg : QuestionFinite 7 7 = false := by
  decide

/-- The source question, formalized as the assertion that some threshold exists
after which every natural number is a sum of at most three powerful numbers. -/
def AllLarge : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsSumOfAtMostThree n

/-- Heath-Brown's resolution of the source question. The mathematical proof of
this literature result remains an explicit honest gap here. -/
theorem heath_brown_result : AllLarge := by
  sorry

#print axioms heath_brown_result

end Erdos941
