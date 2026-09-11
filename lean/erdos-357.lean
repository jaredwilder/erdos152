import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

/-
  The finite predicate below encodes a strictly increasing sequence of integers
  in the interval [1,n], together with injectivity of all its interval sums.
-/

def intervalSum {n k : ℕ} (a : Fin k → Fin (n + 1))
    (u v : Fin k) : ℕ :=
  Finset.sum (Finset.univ.filter (fun i : Fin k => u ≤ i ∧ i ≤ v))
    (fun i => (a i).val)

def GoodSequence (n k : ℕ) (a : Fin k → Fin (n + 1)) : Prop :=
  (∀ i j : Fin k, i < j → (a i).val < (a j).val) ∧
    (∀ i : Fin k, 1 ≤ (a i).val ∧ (a i).val ≤ n) ∧
    (∀ u v u' v' : Fin k,
      u ≤ v →
        u' ≤ v' →
          intervalSum a u v = intervalSum a u' v' →
            u = u' ∧ v = v')

def Admissible (n k : ℕ) : Prop :=
  ∃ a : Fin k → Fin (n + 1), GoodSequence n k a

def f (n : ℕ) : ℕ :=
  Nat.findGreatest (Admissible n) n

def fReal (n : ℕ) : ℝ :=
  f n

theorem witness_pos : Admissible 1 1 := by
  refine ⟨(fun _ : Fin 1 => (⟨1, by decide⟩ : Fin (1 + 1))), ?_⟩
  unfold GoodSequence
  constructor
  · intro i j hij
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst i
    subst j
    simp at hij
  constructor
  · intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    norm_num
  · intro u v u' v' huv huv' heq
    have hu : u = 0 := Fin.eq_zero u
    have hv : v = 0 := Fin.eq_zero v
    have hu' : u' = 0 := Fin.eq_zero u'
    have hv' : v' = 0 := Fin.eq_zero v'
    subst u
    subst v
    subst u'
    subst v'
    exact ⟨rfl, rfl⟩

theorem witness_neg : ¬ Admissible 2 3 := by
  rintro ⟨a, ha⟩
  have h01 := ha.1 (0 : Fin 3) (1 : Fin 3) (by decide)
  have h12 := ha.1 (1 : Fin 3) (2 : Fin 3) (by decide)
  have hb0 := (ha.2.1 (0 : Fin 3)).1
  have hb2 := (ha.2.1 (2 : Fin 3)).2
  omega

theorem open_conjecture :
    fReal =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
  sorry

end