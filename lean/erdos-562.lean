import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
  A colouring is represented on all finite subsets of the vertex set.
  Only subsets having the required cardinality are used as hyperedges,
  so this is equivalent to colouring the edges of the complete uniform
  hypergraph.  The codomain `Bool` represents the two colours.
-/
def IsRamsey (r n m : ℕ) : Prop :=
  ∀ c : Finset (Fin m) → Bool,
    ∃ s : Finset (Fin m),
      s.card = n ∧
        ∀ t u : Finset (Fin m),
          t ⊆ s →
          u ⊆ s →
          t.card = r →
          u.card = r →
          c t = c u

/-- The least number of vertices with the Ramsey property. -/
noncomputable def ramseyNumber (r n : ℕ) : ℕ :=
  sInf {m : ℕ | IsRamsey r n m}

/-- Iterated base-2 logarithm. -/
noncomputable def iteratedLog : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => Real.log (iteratedLog k x) / Real.log 2

/-- A quantitative formulation of the asserted asymptotic estimate. -/
def RamseyAsymptotic (r : ℕ) : Prop :=
  ∃ c C : ℝ,
    0 < c ∧
    0 < C ∧
    ∃ N : ℕ,
      ∀ n : ℕ,
        N ≤ n →
          c * (n : ℝ) ≤
              iteratedLog (r - 1) (ramseyNumber r n : ℝ) ∧
            iteratedLog (r - 1) (ramseyNumber r n : ℝ) ≤ C * (n : ℝ)

/-- At `m = 3`, every 3-uniform colouring contains a monochromatic
    complete 3-uniform hypergraph on 3 vertices. -/
theorem witness_pos : IsRamsey 3 3 3 := by
  intro c
  refine ⟨Finset.univ, ?_, ?_⟩
  · simp
  · intro t u _ _ htcard hucard
    have ht' : t = (Finset.univ : Finset (Fin 3)) := by
      apply Finset.eq_univ_of_card
      simpa using htcard
    have hu' : u = (Finset.univ : Finset (Fin 3)) := by
      apply Finset.eq_univ_of_card
      simpa using hucard
    rw [ht', hu']

/-- With only `m = 2` vertices, there is no 3-vertex monochromatic
    complete 3-uniform hypergraph. -/
theorem witness_neg : ¬ IsRamsey 3 3 2 := by
  intro h
  rcases h (fun _ => false) with ⟨s, hs, _⟩
  have hle : s.card ≤ (Finset.univ : Finset (Fin 2)).card :=
    Finset.card_le_card (Finset.subset_univ s)
  have hle' : s.card ≤ 2 := by
    simpa using hle
  omega

/-- Erdős problem 562: the iterated logarithm of the hypergraph Ramsey
    number has linear growth, with constants depending on `r`. -/
theorem erdos_562 : ∀ r : ℕ, 3 ≤ r → RamseyAsymptotic r := by
  sorry

end