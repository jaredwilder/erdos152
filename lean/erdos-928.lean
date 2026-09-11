import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped Topology
open Filter
def primeDivisors (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun d => d ∣ n ∧ Nat.Prime d)

def largestPrimeDivisor (n : ℕ) : ℕ :=
  if h : (primeDivisors n).Nonempty then
    (primeDivisors n).max' h
  else
    0

def Smooth (α : ℝ) (n : ℕ) : Prop :=
  (largestPrimeDivisor n : ℝ) < (n : ℝ) ^ α

def Event (α β : ℝ) (n : ℕ) : Prop :=
  Smooth α n ∧ Smooth β (n + 1)

noncomputable def eventCount (α β : ℝ) (N : ℕ) : ℕ :=
  (Finset.range N).filter (Event α β) |>.card

noncomputable def eventProportion (α β : ℝ) (N : ℕ) : ℝ :=
  if N = 0 then
    0
  else
    (eventCount α β N : ℝ) / (N : ℝ)

def DensityExists (α β : ℝ) : Prop :=
  ∃ d : ℝ, Filter.Tendsto (eventProportion α β) atTop (𝓝 d)

theorem witness_pos : Event 2 2 1 := by
  have h₁ : largestPrimeDivisor 1 = 0 := by
    decide
  have h₂ : largestPrimeDivisor 2 = 2 := by
    decide
  norm_num [Event, Smooth, h₁, h₂]

theorem witness_neg : ¬ Event 0 0 1 := by
  have h₁ : largestPrimeDivisor 1 = 0 := by
    decide
  have h₂ : largestPrimeDivisor 2 = 2 := by
    decide
  norm_num [Event, Smooth, h₁, h₂]

theorem density_exists
    (α β : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hβ₀ : 0 < β) (hβ₁ : β < 1) :
    DensityExists α β := by
  sorry

end