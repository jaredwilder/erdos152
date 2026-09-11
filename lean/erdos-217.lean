import Mathlib

noncomputable section

abbrev Point := ℝ × ℝ

def distSq (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

def collinearDet (p q r : Point) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

def circleDet (p q r s : Point) : ℝ :=
  Matrix.det ![
    ![p.1, p.2, p.1 ^ 2 + p.2 ^ 2, 1],
    ![q.1, q.2, q.1 ^ 2 + q.2 ^ 2, 1],
    ![r.1, r.2, r.1 ^ 2 + r.2 ^ 2, 1],
    ![s.1, s.2, s.1 ^ 2 + s.2 ^ 2, 1]
  ]

def Pairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

def NoThree (pts : Fin n → Point) : Prop :=
  ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c →
    collinearDet (pts a) (pts b) (pts c) ≠ 0

def NoFour (pts : Fin n → Point) : Prop :=
  ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d →
    b ≠ c → b ≠ d → c ≠ d →
    circleDet (pts a) (pts b) (pts c) (pts d) ≠ 0

def distanceSet (pts : Fin n → Point) : Finset ℝ :=
  by
    classical
    exact (Pairs n).image (fun p => distSq (pts p.1) (pts p.2))

def distanceMultiplicity (pts : Fin n → Point) (d : ℝ) : ℕ :=
  ((Pairs n).filter (fun p => distSq (pts p.1) (pts p.2) = d)).card

def HasRequiredDistances (n : ℕ) : Prop :=
  0 < n ∧
    ∃ pts : Fin n → Point,
      NoThree pts ∧
      NoFour pts ∧
      (distanceSet pts).card = n - 1 ∧
      ∃ ordering : Fin (n - 1) → ℝ,
        Function.Injective ordering ∧
        Finset.univ.image ordering = distanceSet pts ∧
        ∀ i : Fin (n - 1),
          distanceMultiplicity pts (ordering i) = i.1 + 1

def sourceReferenceNumbers : Finset ℕ :=
  {3, 4, 5, 7, 6, 8, 167, 83, 87, 97, 89, 98, 217}

theorem witness_pos : HasRequiredDistances 1 := by
  classical
  simp [HasRequiredDistances, NoThree, NoFour, distanceSet,
    distanceMultiplicity, Pairs, distSq, collinearDet, circleDet]
  intro a b h
  exact Fin.elim0 a

theorem witness_neg : ¬ HasRequiredDistances 0 := by
  simp [HasRequiredDistances]

theorem erdos_217_conjecture :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ HasRequiredDistances n := by
  sorry