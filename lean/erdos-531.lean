import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/- 
Erdős problem 531 ([Er73], [ErSp89], [BENTW17]).
Let F(k) be the minimal N such that if we two-colour {1,...,N}, there is
a set A of size k such that all nonempty subset sums are monochromatic.
The cited lower bound is F(k) ≥ 2^(2^(k-1)/k).
-/

def subsetSum {N : ℕ} (S : Finset (Fin N)) : ℕ :=
  S.sum (fun a => a.1 + 1)

def colorSum (N : ℕ) (c : Fin (N + 1) → Bool) (s : ℕ) (hs : s ≤ N) : Bool :=
  c ⟨s - 1, by omega⟩

def monochromaticSubsetSums (N k : ℕ) (c : Fin (N + 1) → Bool)
    (A : Finset (Fin N)) : Prop :=
  A.card = k ∧
    ∃ b : Bool,
      ∀ S ∈ A.powerset, S.Nonempty →
        ∃ hs : subsetSum S ≤ N,
          colorSum N c (subsetSum S) hs = b

def good (N k : ℕ) : Prop :=
  ∀ c : Fin (N + 1) → Bool,
    ∃ A : Finset (Fin N), monochromaticSubsetSums N k c A

noncomputable def F (k : ℕ) : ℕ := by
  classical
  exact if h : ∃ N : ℕ, good N k then Nat.find h else 0

theorem witness_pos : good 1 1 := by
  intro c
  refine ⟨{0}, ?_⟩
  refine ⟨by simp, c ⟨0, by omega⟩, ?_⟩
  intro S hS hne
  have hSsub : S ⊆ ({0} : Finset (Fin 1)) :=
    Finset.mem_powerset.mp hS
  rcases hne with ⟨x, hx⟩
  have hx0 : x = 0 := by
    have : x ∈ ({0} : Finset (Fin 1)) := hSsub hx
    simpa using this
  have h0 : (0 : Fin 1) ∈ S := hx0 ▸ hx
  have hSeq : S = ({0} : Finset (Fin 1)) := by
    apply Finset.Subset.antisymm hSsub
    intro x hx'
    have hx0' : x = 0 := by simpa using hx'
    simpa [hx0'] using h0
  subst S
  refine ⟨by simp [subsetSum], ?_⟩
  simp [subsetSum, colorSum]

theorem witness_neg : ¬ good 1 2 := by
  intro h
  obtain ⟨A, hA⟩ := h (fun _ => false)
  have hc : A.card ≤ 1 := by
    simpa using (Finset.card_le_univ A)
  have hcard : A.card = 2 := hA.1
  omega

theorem folkman_lower_bound :
    ∀ k : ℕ, 2 ≤ k →
      (F k : ℝ) ≥ (2 : ℝ) ^ (((2 : ℝ) ^ (k - 1)) / (k : ℝ)) := by
  sorry

end