noncomputable section
open scoped BigOperators
def representationCount (A : ℕ → Bool) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter
    (fun a => A a = true ∧ A (n - a) = true)).card

def EventuallyAdditiveBasis (A : ℕ → Bool) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, B ≤ n →
    ∃ a ∈ Finset.range (n + 1), A a = true ∧ A (n - a) = true

def UnboundedRepresentationCount (A : ℕ → Bool) : Prop :=
  ∀ K N : ℕ, ∃ n : ℕ, N ≤ n ∧ K ≤ representationCount A n

def ErdosTuran28 (A : ℕ → Bool) : Prop :=
  EventuallyAdditiveBasis A → UnboundedRepresentationCount A

def coveredUpTo (A : ℕ → Bool) (N : ℕ) : Prop :=
  ((Finset.Icc 1 N).filter
      (fun n => 0 < representationCount A n)).card =
    (Finset.Icc 1 N).card

def hasLargeRepresentation (A : ℕ → Bool) (N K : ℕ) : Prop :=
  ((Finset.Icc 1 N).filter
      (fun n => K ≤ representationCount A n)).Nonempty

def FiniteErdosTuran28 (A : ℕ → Bool) (N K : ℕ) : Prop :=
  coveredUpTo A N → hasLargeRepresentation A N K

theorem witness_pos :
    FiniteErdosTuran28
      (fun n => if n ≤ 2 then true else false) 3 1 := by
  unfold FiniteErdosTuran28 coveredUpTo hasLargeRepresentation representationCount
  decide

theorem witness_neg :
    ¬ FiniteErdosTuran28
      (fun n => if n ≤ 2 then true else false) 3 4 := by
  unfold FiniteErdosTuran28 coveredUpTo hasLargeRepresentation representationCount
  decide

theorem erdos_turan_28 :
    ∀ A : ℕ → Bool, ErdosTuran28 A := by
  sorry

end