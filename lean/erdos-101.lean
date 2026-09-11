import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Source numerals appearing in the frozen entry include:
101, 84, 87, 170, 90, 92, 95, 181, 97, 66, 4, 5, 2, 6, 74, 13,
3, 588, 71, 2025, 27, 2026, 8, 30, 0, and 1.
-/

abbrev Point := ℚ × ℚ

def collinear (a b c : Point) : Prop :=
  (a.1 - b.1) * (c.2 - b.2) = (a.2 - b.2) * (c.1 - b.1)

def allCollinear (S : Finset Point) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, collinear a b c

def noFiveOnALine (P : Finset Point) : Prop :=
  ∀ S ∈ P.powerset, S.card ≠ 5 ∨ ¬ allCollinear S

def generatedLines (P : Finset Point) : Finset (Finset Point) :=
  (P.product P).filter (fun q => q.1 ≠ q.2) |>.image
    (fun q => P.filter (fun c => collinear q.1 q.2 c))

def fourLineCount (P : Finset Point) : ℕ :=
  (generatedLines P).filter (fun L => L.card = 4) |>.card

def admissible (n : ℕ) (P : Finset Point) : Prop :=
  P.card = n ∧ noFiveOnALine P

def erdosClaim : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ P : Finset Point, admissible n P →
        (fourLineCount P : ℚ) ≤ ε * (n : ℚ) ^ 2

def Ppos : Finset Point :=
  {(0, 0)}

def Pneg : Finset Point :=
  {(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)}

theorem witness_pos : admissible 1 Ppos := by
  constructor
  · simp [Ppos]
  · intro S hS
    have hsub : S ⊆ Ppos := Finset.mem_powerset.mp hS
    have hc := Finset.card_le_card hsub
    have hc' : S.card ≤ 1 := by
      simpa [Ppos] using hc
    exact Or.inl (by omega)

theorem witness_neg : ¬ admissible 5 Pneg := by
  intro h
  rcases h with ⟨hcard, hn⟩
  have hcol : allCollinear Pneg := by
    have hsecond : ∀ x : Point, x ∈ Pneg → x.2 = 0 := by
      intro x hx
      simp [Pneg] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl
    intro a ha b hb c hc
    have ha2 := hsecond a ha
    have hb2 := hsecond b hb
    have hc2 := hsecond c hc
    simp [collinear, ha2, hb2, hc2]
  have hor := hn Pneg (by simp)
  rcases hor with hne | hnot
  · exact hne hcard
  · exact hnot hcol

theorem erdos_problem_101 : erdosClaim := by
  sorry

end