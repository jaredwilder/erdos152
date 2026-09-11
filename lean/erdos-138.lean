import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/- 
The source discusses 2-colourings, W(k), the bounds p+1, p2^p, 2^k,
the 3-colour analogue, the constant C>1, the reward $500, and the
dates 2026-06-02 and 2026-08-30.  The formalization below uses finite
colourings so that its small witnesses are kernel-decidable.
-/

/-- A monochromatic arithmetic progression of length `k` in `Fin N`. -/
def HasMonoAP (k N : ℕ) (c : Fin N → Bool) : Prop :=
  ∃ a : Fin N, ∃ d : Fin (N + 1),
    d.val > 0 ∧
      ∀ i : Fin k,
        ∃ x : Fin N,
          x.val = a.val + i.val * d.val ∧ c x = c a

/-- Every 2-colouring of `Fin N` contains a monochromatic `k`-term progression. -/
def VanDerWaerdenProperty (k N : ℕ) : Prop :=
  ∀ c : Fin N → Bool, HasMonoAP k N c

/-- `w` is the least finite witness for the van der Waerden property. -/
def IsVanDerWaerdenNumber (k w : ℕ) : Prop :=
  VanDerWaerdenProperty k w ∧
    ∀ n ∈ Finset.range w, ¬ VanDerWaerdenProperty k n

theorem witness_pos : IsVanDerWaerdenNumber 1 1 := by
  constructor
  · intro c
    refine ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide, ?_⟩
    intro i
    have hi : i.val = 0 := by omega
    refine ⟨⟨0, by decide⟩, ?_, ?_⟩
    · simp [hi]
    · simp
  · intro n hn
    have hnlt : n < 1 := by simpa using hn
    have hn0 : n = 0 := by omega
    subst n
    intro hp
    rcases hp (fun _ => false) with ⟨a, d, hd, hall⟩
    exact Fin.elim0 a

theorem witness_neg : ¬ IsVanDerWaerdenNumber 2 1 := by
  intro h
  rcases h.1 (fun _ => false) with ⟨a, d, hd, hall⟩
  obtain ⟨x, hx, hcx⟩ := hall ⟨1, by decide⟩
  have hxlt : x.val < 1 := x.isLt
  have hxeq : x.val = a.val + d.val := by
    simpa using hx
  omega

/-- The open conjecture that the `k`-th root of the van der Waerden
number tends to infinity. -/
def RootGrowth (W : ℕ → ℕ) : Prop :=
  Filter.Tendsto
    (fun k : ℕ => ((W k : ℝ) ^ (1 / (k : ℝ))))
    Filter.atTop Filter.atTop

theorem van_der_waerden_root_growth :
    ∀ W : ℕ → ℕ,
      (∀ k : ℕ, IsVanDerWaerdenNumber k (W k)) →
        RootGrowth W := by
  sorry

end