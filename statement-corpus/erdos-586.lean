/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is there a covering system such that no two of the moduli divide each other?

NODE n001-resolution (resolution), VERBATIM:
#586 : [ErGr80] [Er96b] [Er97] [Er97c] [Er97e] number theory | covering systems Asked by Schinzel, motivated by a question of Erdős and Selfridge (see [7] ). The answer is no, as proved by Balister, Bollobás, Morris, Sahasrabudhe, and Tiba [BBMST22] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #586, https://www.erdosproblems.com/586, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


-- @category research solved

import Mathlib
open Classical








open Classical Filter

namespace Erdos586

/-- A finite covering system is represented by finitely many pairs `(m, r)`,
where `m` is a modulus and `r` is a residue. Every natural number belongs to
at least one of the corresponding congruence classes, and all moduli are at
least two. -/
def IsCovering (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ n : ℕ, ∃ p ∈ S, 2 ≤ p.1 ∧ n % p.1 = p.2 % p.1

/-- `PairwiseNondividing S` says that for two distinct members of the
covering system, the modulus of neither member divides the modulus of the
other. -/
def PairwiseNondividing (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ ⦃p q : ℕ × ℕ⦄, p ∈ S → q ∈ S → p ≠ q → ¬ p.1 ∣ q.1

/-- The literal formalization of the question asks whether a finite covering
system can have pairwise nondividing moduli. -/
def Question : Prop :=
  ∃ S : Finset (ℕ × ℕ), IsCovering S ∧ PairwiseNondividing S

/-- The empty finite family is not a covering system; this control exercises
the existential coverage condition in `IsCovering`. -/
theorem empty_not_covering :
    ¬ IsCovering (∅ : Finset (ℕ × ℕ)) := by
  intro h
  obtain ⟨p, hp, _⟩ := h 0
  simp at hp

/-- The two parity classes form a covering system, giving a concrete
non-vacuity control for the congruence-class definition. -/
theorem parity_covering :
    IsCovering ({(2, 0), (2, 1)} : Finset (ℕ × ℕ)) := by
  intro n
  have h : n % 2 = 0 ∨ n % 2 = 1 := by
    omega
  rcases h with h | h
  · refine ⟨(2, 0), by simp, ?_⟩
    constructor
    · norm_num
    · simpa using h
  · refine ⟨(2, 1), by simp, ?_⟩
    constructor
    · norm_num
    · simpa using h

/-- The parity covering does not have pairwise nondividing moduli, since its
two distinct moduli are both equal to two. -/
theorem parity_not_pairwise_nondividing :
    ¬ PairwiseNondividing ({(2, 0), (2, 1)} : Finset (ℕ × ℕ)) := by
  intro h
  have hnotdvd :
      ¬ ((2 : ℕ) ∣ 2) :=
    h (p := (2, 0)) (q := (2, 1)) (by simp) (by simp) (by decide)
  exact hnotdvd (dvd_refl 2)

/-- The resolved answer to Erdos problem 586 is negative. The source states
that no covering system exists whose moduli are pairwise nondividing; the
formal proof of this theorem remains to be supplied from the cited result
[BBMST22].

Source-to-statement mapping: “a covering system” is `IsCovering S`, and “no
two of the moduli divide each other” is `PairwiseNondividing S`, so the
question is formalized as `Question`; the recorded resolution “The answer is
no” is `¬ Question`. -/
theorem no_covering_system_with_nondividing_moduli :
    ¬ Question := by
  sorry

#print axioms no_covering_system_with_nondividing_moduli

end Erdos586
