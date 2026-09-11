import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def sourceNumerals : List ℕ :=
  [530, 73, 120, 75, 104, 80, 109, 80, 3, 1, 2, 85, 69, 1088, 1208,
    9, 4, 143824, 2026, 8, 30, 0, 1]

def IsSidon {B : ℕ} (S : Finset (Fin B)) : Prop :=
  ∀ a b c d : Fin B,
    a ∈ S →
    b ∈ S →
    c ∈ S →
    d ∈ S →
    a.val + b.val = c.val + d.val →
      ((a = c ∧ b = d) ∨ (a = d ∧ b = c))

def HasSidonSubset {B : ℕ} (A : Finset (Fin B)) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin B), S ⊆ A ∧ S.card = k ∧ IsSidon S

def Good (N k : ℕ) : Prop :=
  ∀ B : ℕ, ∀ A : Finset (Fin B), A.card = N → HasSidonSubset A k

noncomputable def ell (N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun k => Good N k) N

theorem witness_pos :
    HasSidonSubset (Finset.univ : Finset (Fin 3)) 2 := by
  refine ⟨{0, 1}, by simp, by decide, ?_⟩
  intro a b c d ha hb hc hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc hd
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

theorem witness_neg :
    ¬ HasSidonSubset (Finset.univ : Finset (Fin 3)) 3 := by
  rintro ⟨S, hsub, hcard, hsidon⟩
  have hS : S = (Finset.univ : Finset (Fin 3)) := by
    apply Finset.eq_univ_of_card
    simpa using hcard
  have hbad := hsidon (0 : Fin 3) 2 1 1 (by simp [hS]) (by simp [hS])
    (by simp [hS]) (by simp [hS]) (by norm_num)
  norm_num at hbad

theorem main_conjecture :
    Filter.Tendsto (fun N : ℕ => (ell N : ℝ) / Real.sqrt (N : ℝ)) Filter.atTop (nhds (1 : ℝ)) := by
  sorry

end