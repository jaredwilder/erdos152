-- Erdos problem 1160.  The source also mentions 22.16, 22.18, 3619, 7,
-- 0, 3, 2026-01-26, 2026-08-30, and OEIS A000001.

import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def IsGroupTable (n : Nat) (t : Fin n → Fin n → Fin n) : Prop :=
  ∃ e : Fin n,
    (∀ a, t e a = a ∧ t a e = a) ∧
    (∀ a b c, t (t a b) c = t a (t b c)) ∧
    (∀ a, ∃ b, t a b = e ∧ t b a = e)

def tableCode {n : Nat} (t : Fin n → Fin n → Fin n) : Nat :=
  ∑ a : Fin n, ∑ b : Fin n,
    (n + 1) ^ (a.val * n + b.val) * (t a b).val

def transportedTable {n : Nat} (t : Fin n → Fin n → Fin n)
    (σ : Equiv.Perm (Fin n)) : Fin n → Fin n → Fin n :=
  fun a b => σ.symm (t (σ a) (σ b))

def IsCanonicalTable {n : Nat} (t : Fin n → Fin n → Fin n) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    tableCode t ≤ tableCode (transportedTable t σ)

def groupCount (n : Nat) : Nat :=
  ((Finset.univ : Finset (Fin n → Fin n → Fin n)).filter
      (fun t => IsGroupTable n t ∧ IsCanonicalTable t)).card

def groupInequality (n k : Nat) : Prop :=
  groupCount n ≤ groupCount k

def erdos1160 : Prop :=
  ∀ n m : Nat, n ≤ 2 ^ m → groupInequality n (2 ^ m)

theorem witness_pos : groupInequality 1 1 := by
  classical
  have h1 : ∀ t : Fin 1 → Fin 1 → Fin 1,
      IsGroupTable 1 t ∧ IsCanonicalTable t := by
    intro t
    constructor
    · refine ⟨0, ?_, ?_, ?_⟩
      · intro a
        constructor <;> apply Subsingleton.elim
      · intro a b c
        apply Subsingleton.elim
      · intro a
        refine ⟨0, ?_, ?_⟩ <;> apply Subsingleton.elim
    · intro σ
      have ht : transportedTable t σ = t := by
        funext a b
        apply Subsingleton.elim
      rw [ht]
  have hc1 :
      ((Finset.univ : Finset (Fin 1 → Fin 1 → Fin 1)).filter
        (fun t => IsGroupTable 1 t ∧ IsCanonicalTable t)) =
        Finset.univ := by
    ext t
    simp [h1]
  have gc1 : groupCount 1 = 1 := by
    rw [groupCount, hc1]
    simp
  simp [groupInequality, gc1]

theorem witness_neg : ¬ groupInequality 1 0 := by
  classical
  have h0 : ∀ t : Fin 0 → Fin 0 → Fin 0, ¬ IsGroupTable 0 t := by
    intro t h
    rcases h with ⟨e, _⟩
    exact Fin.elim0 e
  have hc0 :
      ((Finset.univ : Finset (Fin 0 → Fin 0 → Fin 0)).filter
        (fun t => IsGroupTable 0 t ∧ IsCanonicalTable t)) =
        ∅ := by
    ext t
    simp [h0]
  have gc0 : groupCount 0 = 0 := by
    rw [groupCount, hc0]
    simp
  have h1 : ∀ t : Fin 1 → Fin 1 → Fin 1,
      IsGroupTable 1 t ∧ IsCanonicalTable t := by
    intro t
    constructor
    · refine ⟨0, ?_, ?_, ?_⟩
      · intro a
        constructor <;> apply Subsingleton.elim
      · intro a b c
        apply Subsingleton.elim
      · intro a
        refine ⟨0, ?_, ?_⟩ <;> apply Subsingleton.elim
    · intro σ
      have ht : transportedTable t σ = t := by
        funext a b
        apply Subsingleton.elim
      rw [ht]
  have hc1 :
      ((Finset.univ : Finset (Fin 1 → Fin 1 → Fin 1)).filter
        (fun t => IsGroupTable 1 t ∧ IsCanonicalTable t)) =
        Finset.univ := by
    ext t
    simp [h1]
  have gc1 : groupCount 1 = 1 := by
    rw [groupCount, hc1]
    simp
  simp [groupInequality, gc1, gc0]

theorem erdos_1160 : erdos1160 := by
  sorry

end