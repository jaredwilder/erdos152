import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def validElement (N : ℕ) (x : Fin (N + 1)) : Prop :=
  1 ≤ x.val

def IsSidon {N : ℕ} (A : Finset (Fin (N + 1))) : Prop :=
  ∀ a b c d : Fin (N + 1),
    a ∈ A →
    b ∈ A →
    c ∈ A →
    d ∈ A →
    a ≠ b →
    c ≠ d →
    a.val + b.val = c.val + d.val →
    ((a = c ∧ b = d) ∨ (a = d ∧ b = c))

def Good (N C : ℕ) : Prop :=
  ∃ A : Finset (Fin (N + 1)),
    (∀ x ∈ A, validElement N x) ∧
    IsSidon A ∧
    (∀ x : Fin (N + 1),
      validElement N x →
      x ∉ A →
      ¬ IsSidon (insert x A)) ∧
    A.card ^ 3 ≤ C ^ 3 * N

theorem witness_pos : Good 1 1 := by
  have only_one : ∀ x : Fin 2, validElement 1 x → x = (1 : Fin 2) := by
    intro x hx
    fin_cases x <;> simp [validElement] at hx ⊢
  have hsingleton : IsSidon ({(1 : Fin 2)} : Finset (Fin 2)) := by
    intro a b c d ha hb hc hd hab hcd hsum
    have ha' : a = (1 : Fin 2) := by simpa using ha
    have hb' : b = (1 : Fin 2) := by simpa using hb
    have hc' : c = (1 : Fin 2) := by simpa using hc
    have hd' : d = (1 : Fin 2) := by simpa using hd
    subst a
    subst b
    subst c
    subst d
    exact (hab rfl).elim
  refine ⟨{(1 : Fin 2)}, ?_, hsingleton, ?_, ?_⟩
  · intro x hx
    have hx' : x = (1 : Fin 2) := by simpa using hx
    rw [hx']
    simp [validElement]
  · intro x hxv hxnot
    have hx' := only_one x hxv
    subst x
    exact (hxnot (by simp)).elim
  · norm_num

theorem witness_neg : ¬ Good 1 0 := by
  have only_one : ∀ x : Fin 2, validElement 1 x → x = (1 : Fin 2) := by
    intro x hx
    fin_cases x <;> simp [validElement] at hx ⊢
  have hsingleton : IsSidon ({(1 : Fin 2)} : Finset (Fin 2)) := by
    intro a b c d ha hb hc hd hab hcd hsum
    have ha' : a = (1 : Fin 2) := by simpa using ha
    have hb' : b = (1 : Fin 2) := by simpa using hb
    have hc' : c = (1 : Fin 2) := by simpa using hc
    have hd' : d = (1 : Fin 2) := by simpa using hd
    subst a
    subst b
    subst c
    subst d
    exact (hab rfl).elim
  intro h
  rcases h with ⟨A, hvalid, hsidon, hmax, hbound⟩
  by_cases h1 : (1 : Fin 2) ∈ A
  · have hsub : A = {(1 : Fin 2)} := by
      ext x
      constructor
      · intro hx
        have hxv := hvalid x hx
        have hx' := only_one x hxv
        rw [hx']
        simp
      · intro hx
        have hx' : x = (1 : Fin 2) := by simpa using hx
        rw [hx']
        exact h1
    norm_num [hsub] at hbound
  · have hempty : A = ∅ := by
      ext x
      constructor
      · intro hx
        have hxv := hvalid x hx
        have hx' := only_one x hxv
        exfalso
        apply h1
        rw [← hx']
        exact hx
      · intro hx
        simp at hx
    have hn := hmax (1 : Fin 2) (by simp [validElement]) h1
    apply hn
    simpa [hempty] using hsingleton

theorem erdos_problem_156 :
    ∃ C : ℕ, ∀ N : ℕ, 1 ≤ N → Good N C := by
  sorry

end