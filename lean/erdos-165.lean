import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def Coloring (n : ℕ) := Edge n → Bool

def monochromatic {n : ℕ} (c : Coloring n) (s : Finset (Fin n))
    (b : Bool) : Prop :=
  ∀ ⦃u v : Fin n⦄ (hu : u ∈ s) (hv : v ∈ s) ( huv : u < v),
    c ⟨(u, v), huv⟩ = b

def hasClique (n r : ℕ) (c : Coloring n) (b : Bool) : Prop :=
  ∃ s : Finset (Fin n), s.card = r ∧ monochromatic c s b

def ramseyProperty (n k : ℕ) : Prop :=
  ∀ c : Coloring n,
    hasClique n 3 c true ∨ hasClique n k c false

theorem witness_pos : ramseyProperty 3 1 := by
  intro c
  right
  refine ⟨{(0 : Fin 3)}, by simp, ?_⟩
  intro u v hu hv huv
  simp only [Finset.mem_singleton] at hu hv
  subst u
  subst v
  exact (lt_irrefl 0 huv).elim

theorem witness_neg : ¬ ramseyProperty 2 2 := by
  intro h
  let c : Coloring 2 := fun _ => true
  rcases h c with h3 | h2
  · rcases h3 with ⟨s, hs, _⟩
    have hc : s.card ≤ 2 := by
      simpa using (Finset.card_le_univ s)
    rw [hs] at hc
    omega
  · rcases h2 with ⟨s, hs, hm⟩
    have h0 : (0 : Fin 2) ∈ s := by
      by_contra hn
      have hsub : s ⊆ ({1} : Finset (Fin 2)) := by
        intro x hx
        fin_cases x
        · exact (hn hx).elim
        · simp
      have hcard := Finset.card_le_card hsub
      simp at hcard
      omega
    have h1 : (1 : Fin 2) ∈ s := by
      by_contra hn
      have hsub : s ⊆ ({0} : Finset (Fin 2)) := by
        intro x hx
        fin_cases x
        · simp
        · exact (hn hx).elim
      have hcard := Finset.card_le_card hsub
      simp at hcard
      omega
    have he := hm (u := (0 : Fin 2)) (v := 1) h0 h1 (by norm_num)
    simpa [c] using he

noncomputable def ramseyNumber (k : ℕ) : ℕ :=
  sInf {n : ℕ | ramseyProperty 3 k}

def scaledRamseyRatio (k : ℕ) : ℝ :=
  (ramseyNumber k : ℝ) * Real.log (k : ℝ) / (k : ℝ) ^ 2

def asymptoticRamseyBounds : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ ε : ℝ, 0 < ε →
      (∀ᶠ k : ℕ in Filter.atTop,
        c - ε ≤ scaledRamseyRatio k ∧
        scaledRamseyRatio k ≤ 1 + ε)

def sourceLowerConstants : List ℝ :=
  [1 / 162, 1 / 4, 1 / 3, 1 / 2]

def sourceReferenceNumbers : List ℕ :=
  [95, 83, 80, 21, 20, 25, 25, 544, 986, 1013]

theorem ramsey_asymptotic_formula : asymptoticRamseyBounds := by
  sorry

end