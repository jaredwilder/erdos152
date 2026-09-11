import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def TriangleFree {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c : Fin n,
    a ≠ b →
    a ≠ c →
    b ≠ c →
    ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)

def IndependentOn {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬G.Adj x y

def HasIndependent {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card = k ∧ IndependentOn G S

def Clique {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y

def MaximalClique {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  Clique G S ∧ ∀ v, v ∉ S → ∃ u ∈ S, ¬G.Adj v u

def CliqueTransversal {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ S : Finset (Fin n),
    MaximalClique G S →
    2 ≤ S.card →
    ∃ v, v ∈ T ∧ v ∈ S

def CliqueTransversalNumberLE {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) : Prop :=
  ∃ T : Finset (Fin n), T.card ≤ q ∧ CliqueTransversal G T

def H (n : ℕ) : ℕ :=
  (Finset.filter
      (fun k => ∀ G : SimpleGraph (Fin n), TriangleFree G → HasIndependent G k)
      (Finset.range (n + 1))).max'
    (by
      have hmem :
          0 ∈
            Finset.filter
              (fun k => ∀ G : SimpleGraph (Fin n), TriangleFree G → HasIndependent G k)
              (Finset.range (n + 1)) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · exact Nat.zero_lt_succ n
        · intro G hG
          refine ⟨∅, ?_⟩
          simp [IndependentOn]
      exact ⟨0, hmem⟩)

theorem witness_pos :
    CliqueTransversalNumberLE (⊥ : SimpleGraph (Fin 1)) 0 := by
  refine ⟨∅, by simp, ?_⟩
  intro S _ hcard
  have hle : S.card ≤ (Finset.univ : Finset (Fin 1)).card :=
    Finset.card_le_card (Finset.subset_univ S)
  have hle' : S.card ≤ 1 := by
    simpa using hle
  omega

theorem witness_neg :
    ¬CliqueTransversalNumberLE (⊤ : SimpleGraph (Fin 2)) 0 := by
  intro h
  rcases h with ⟨T, hcard, hT⟩
  have hTzero : T.card = 0 := by
    omega
  have hTempty : T = ∅ := Finset.card_eq_zero.mp hTzero
  subst T
  have hmax :
      MaximalClique (⊤ : SimpleGraph (Fin 2))
        (Finset.univ : Finset (Fin 2)) := by
    simp [MaximalClique, Clique]
  have hcard' : 2 ≤ (Finset.univ : Finset (Fin 2)).card := by
    simp
  obtain ⟨v, hv, _⟩ := hT _ hmax hcard'
  simpa using hv

theorem conjecture :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      CliqueTransversalNumberLE G (n - H n) := by
  sorry

end