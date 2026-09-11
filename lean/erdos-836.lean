import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def Monochromatic {n k : ℕ} (e : Finset (Fin n)) (c : Fin n → Fin k) : Prop :=
  ∀ ⦃v⦄, v ∈ e → ∀ ⦃w⦄, w ∈ e → c v = c w

def Colorable (k n : ℕ) (G : Finset (Finset (Fin n))) : Prop :=
  ∃ c : Fin n → Fin k, ∀ e ∈ G, ¬ Monochromatic e c

def Uniform {n r : ℕ} (G : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ G, e.card = r

def Intersecting {n : ℕ} (G : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ G, ∀ f ∈ G, (e ∩ f).Nonempty

def HypergraphCondition (r n : ℕ) (G : Finset (Finset (Fin n))) : Prop :=
  2 ≤ r ∧
    (∀ e ∈ G, e.Nonempty) ∧
    Uniform (r := r) G ∧
    Intersecting G ∧
    Colorable 3 n G ∧
    ¬ Colorable 2 n G

def vertexCount {n : ℕ} (G : Finset (Finset (Fin n))) : ℕ :=
  (G.biUnion (fun e => e)).card

def BoundedVertices : Prop :=
  ∃ C : ℕ,
    ∀ (r n : ℕ) (G : Finset (Finset (Fin n))),
      HypergraphCondition r n G →
        vertexCount G ≤ C * r ^ 2

def IntersectionGuarantee : Prop :=
  ∃ c R : ℕ,
    0 < c ∧
      ∀ (r n : ℕ) (G : Finset (Finset (Fin n))),
        R ≤ r →
          HypergraphCondition r n G →
            ∃ e ∈ G, ∃ f ∈ G,
              c * r ≤ (e ∩ f).card * Nat.log r

def triangle : Finset (Finset (Fin 3)) :=
  {({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3))}

def singleEdge : Finset (Finset (Fin 2)) :=
  {({0, 1} : Finset (Fin 2))}

theorem witness_pos : HypergraphCondition 2 3 triangle := by
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    simp [triangle] at he
    rcases he with rfl | rfl | rfl <;> simp
  · intro e he
    simp [triangle] at he
    rcases he with rfl | rfl | rfl <;> simp
  · intro e he f hf
    simp [triangle] at he hf
    rcases he with rfl | rfl | rfl <;>
      rcases hf with rfl | rfl | rfl <;>
      simp
  · refine ⟨fun v : Fin 3 => v, ?_⟩
    intro e he
    simp [triangle] at he
    rcases he with rfl | rfl | rfl
    · intro h
      have h' := h (v := (0 : Fin 3)) (by simp) (w := (1 : Fin 3)) (by simp)
      simpa using h'
    · intro h
      have h' := h (v := (0 : Fin 3)) (by simp) (w := (2 : Fin 3)) (by simp)
      simpa using h'
    · intro h
      have h' := h (v := (1 : Fin 3)) (by simp) (w := (2 : Fin 3)) (by simp)
      simpa using h'
  · intro h
    rcases h with ⟨c, hc⟩
    have h01 : c 0 ≠ c 1 := by
      intro h01
      apply hc ({0, 1} : Finset (Fin 3)) (by simp [triangle])
      intro v hv w hw
      fin_cases v <;> fin_cases w <;> simp_all
    have h02 : c 0 ≠ c 2 := by
      intro h02
      apply hc ({0, 2} : Finset (Fin 3)) (by simp [triangle])
      intro v hv w hw
      fin_cases v <;> fin_cases w <;> simp_all
    have h12 : c 1 ≠ c 2 := by
      intro h12
      apply hc ({1, 2} : Finset (Fin 3)) (by simp [triangle])
      intro v hv w hw
      fin_cases v <;> fin_cases w <;> simp_all
    generalize ha : c 0 = a
    generalize hb : c 1 = b
    generalize hd : c 2 = d
    fin_cases a <;> fin_cases b <;> fin_cases d <;> simp_all

theorem witness_neg : ¬ HypergraphCondition 2 2 singleEdge := by
  intro h
  have hcol := h.2.2.2.2.2
  apply hcol
  refine ⟨fun v : Fin 2 => v, ?_⟩
  intro e he
  simp [singleEdge] at he
  rcases he with rfl
  intro hm
  have h01 := hm (v := (0 : Fin 2)) (by simp) (w := (1 : Fin 2)) (by simp)
  simpa using h01

theorem erdos_836 : ¬ BoundedVertices ∧ IntersectionGuarantee := by
  sorry

end