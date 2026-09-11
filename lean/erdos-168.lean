import Mathlib


noncomputable section
open scoped BigOperators Topology
open Filter
def sourceProblemNumber : ℕ := 168

def sourceEstimate : ℝ := 0.800965

def TripleFree (N : ℕ) (s : Finset ℕ) : Prop :=
  s ⊆ Finset.Icc 1 N ∧
    ∀ n ∈ Finset.Icc 1 N, ¬ (n ∈ s ∧ 2 * n ∈ s ∧ 3 * n ∈ s)

theorem witness_pos : TripleFree 3 ({1, 2} : Finset ℕ) := by
  unfold TripleFree
  constructor
  · intro n hn
    simp at hn ⊢
    omega
  · intro n hn hbad
    rcases hbad with ⟨h1, h2, h3⟩
    simp at h1 h2 h3
    omega

theorem witness_neg : ¬ TripleFree 3 ({1, 2, 3} : Finset ℕ) := by
  intro h
  have hbad := h.2 1 (by simp)
  apply hbad
  norm_num

def admissibleCards (N : ℕ) : Finset ℕ := by
  classical
  exact
    ((Finset.Icc 1 N).powerset.filter (TripleFree N)).image (fun s => s.card)

theorem admissibleCards_nonempty (N : ℕ) :
    (admissibleCards N).Nonempty := by
  refine ⟨0, ?_⟩
  refine Finset.mem_image.mpr ⟨(∅ : Finset ℕ), ?_, ?_⟩
  · simp [TripleFree]
  · simp

def F (N : ℕ) : ℕ :=
  (admissibleCards N).max' (admissibleCards_nonempty N)

def density (N : ℕ) : ℝ :=
  (F N : ℝ) / (N : ℝ)

theorem erdos_problem_168 :
    ∃ L : ℝ, Tendsto density atTop (𝓝 L) ∧ Irrational L := by
  sorry

end