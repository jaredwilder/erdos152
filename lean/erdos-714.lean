import Mathlib

noncomputable section
open scoped BigOperators
open scoped Classical
def problemNumber : Nat := 714

def knownSmallParameter : Nat := 2

def knownCubicParameter : Nat := 3

def edgeUniverse (n : Nat) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)

def graphAdjacent {n : Nat} (E : Finset (Fin n × Fin n))
    (u v : Fin n) : Prop :=
  u ≠ v ∧
    if u < v then (u, v) ∈ E else (v, u) ∈ E

def containsKrr (n r : Nat) (E : Finset (Fin n × Fin n)) : Prop :=
  ∃ f : Fin r → Fin n, Function.Injective f ∧
    ∃ g : Fin r → Fin n, Function.Injective g ∧
      (∀ i j, f i ≠ g j ∧ graphAdjacent E (f i) (g j))

def krrFree (n r : Nat) (E : Finset (Fin n × Fin n)) : Prop :=
  ¬ containsKrr n r E

def hasLargeFreeGraph (n r k : Nat) : Prop :=
  ((edgeUniverse n).powerset.filter
      (fun E => krrFree n r E ∧ k ≤ E.card)).Nonempty

def erdos714Conjecture : Prop :=
  ∀ r : Nat, 2 ≤ r →
    ∃ a b N : Nat, 0 < a ∧ 0 < b ∧
      ∀ n : Nat, N ≤ n →
        ∃ k : Nat,
          hasLargeFreeGraph n r k ∧
            a * n ^ (2 * r - 1) ≤ b * k ^ r

theorem witness_pos : hasLargeFreeGraph 1 2 0 := by
  classical
  have hE : edgeUniverse 1 = ∅ := by
    ext p
    have hp : p.1 = p.2 := Subsingleton.elim _ _
    simp [edgeUniverse, hp]
  rw [hasLargeFreeGraph, hE]
  refine ⟨∅, ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_powerset.mpr (by simp)
  · constructor
    · change ¬ containsKrr 1 2 (∅ : Finset (Fin 1 × Fin 1))
      intro h
      rcases h with ⟨f, hf, g, hg, hcross⟩
      have hc := Fintype.card_le_of_injective f hf
      norm_num at hc
    · simp

theorem witness_neg : ¬ hasLargeFreeGraph 1 2 1 := by
  classical
  have hE : edgeUniverse 1 = ∅ := by
    ext p
    have hp : p.1 = p.2 := Subsingleton.elim _ _
    simp [edgeUniverse, hp]
  rw [hasLargeFreeGraph, hE]
  intro h
  rcases h with ⟨E, hE_mem⟩
  have hsub : E ⊆ (∅ : Finset (Fin 1 × Fin 1)) :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hE_mem).1
  have heq : E = ∅ :=
    Finset.Subset.antisymm hsub (Finset.empty_subset _)
  have hk : 1 ≤ E.card := (Finset.mem_filter.mp hE_mem).2.2
  rw [heq] at hk
  norm_num at hk

theorem erdos_714 : erdos714Conjecture := by
  sorry

end