import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-- A finite indexed set of real numbers is dissociated when its subset sums
are all distinct. -/
def RealDissociated {n : ℕ} (a : Fin n → ℝ) (B : Finset (Fin n)) : Prop :=
  ∀ S T : Finset (Fin n),
    S ⊆ B →
    T ⊆ B →
    (S.sum (fun i => a i) = T.sum (fun i => a i)) →
    S = T

/-- There is a dissociated subset of the indexed configuration of size at
least `k`. -/
def HasRealDissociatedSubset (a : Fin n → ℝ) (k : ℕ) : Prop :=
  ∃ B : Finset (Fin n),
    k ≤ B.card ∧ RealDissociated a B

/-- The assertion that every finite real configuration of size `n` has a
dissociated subset of size at least `k`.  Injectivity makes the indexed
configuration represent a set rather than a multiset. -/
def EveryRealConfiguration (n k : ℕ) : Prop :=
  ∀ a : Fin n → ℝ, Function.Injective a →
    HasRealDissociatedSubset a k

/-- The greedy lower-bound exponent appearing in the known result. -/
def greedyExponent (n : ℕ) : ℕ :=
  Nat.log 3 n

/-- The conjectured exponent from the question. -/
def conjecturedExponent (n : ℕ) : ℕ :=
  Nat.log 2 n

theorem witness_pos :
    HasRealDissociatedSubset (fun _ : Fin 1 => (1 : ℝ)) 1 := by
  refine ⟨{0}, by norm_num, ?_⟩
  intro S T hS hT hEq
  have hS' : S ⊆ ({0} : Finset (Fin 1)) := by
    simpa using hS
  have hT' : T ⊆ ({0} : Finset (Fin 1)) := by
    simpa using hT
  have hS'' : S = ∅ ∨ S = ({0} : Finset (Fin 1)) :=
    Finset.subset_singleton_iff.mp hS'
  have hT'' : T = ∅ ∨ T = ({0} : Finset (Fin 1)) :=
    Finset.subset_singleton_iff.mp hT'
  rcases hS'' with rfl | rfl <;> rcases hT'' with rfl | rfl
  · rfl
  · norm_num at hEq
  · norm_num at hEq
  · rfl

theorem witness_neg :
    ¬ HasRealDissociatedSubset (fun _ : Fin 2 => (0 : ℝ)) 3 := by
  rintro ⟨B, hB, _⟩
  have hle : B.card ≤ (Finset.univ : Finset (Fin 2)).card :=
    Finset.card_le_card (Finset.subset_univ B)
  simp at hle
  omega

/-- Formal statement of the proposed lower bound
`f(n) ≥ floor (log_2 n)` in the finite real formulation. -/
theorem conjectured_log_two_lower_bound :
    ∀ n : ℕ, 0 < n → EveryRealConfiguration n (conjecturedExponent n) := by
  sorry

end