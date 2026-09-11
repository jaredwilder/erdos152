import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
structure GraphData where
  n : ℕ
  edges : Finset (Fin n × Fin n)
  k : ℕ
  cycleLengths : Finset ℕ

def edgeCount (G : GraphData) : ℕ :=
  G.edges.card

def reciprocalCycleSum (G : GraphData) : ℚ :=
  G.cycleLengths.sum (fun a => (1 : ℚ) / (a : ℚ))

def densityCondition (G : GraphData) : Prop :=
  edgeCount G = G.k * G.n

def lowerBoundCondition (G : GraphData) : Prop :=
  reciprocalCycleSum G ≥ (Nat.log 2 G.k : ℚ)

def claimAt (G : GraphData) : Prop :=
  densityCondition G ∧ lowerBoundCondition G

def erdosLowerBound : Prop :=
  ∀ G : GraphData, densityCondition G → lowerBoundCondition G

def isCompleteBipartite (G : GraphData) : Prop :=
  ∃ A B : Finset (Fin G.n),
    Disjoint A B ∧
      A ∪ B = Finset.univ ∧
        G.edges = (A.product B) ∪ (B.product A)

def minimizesFor (G H : GraphData) : Prop :=
  G.n = H.n →
    G.k = H.k →
      densityCondition H →
        reciprocalCycleSum G ≤ reciprocalCycleSum H

def completeBipartiteMinimizer : Prop :=
  ∀ G : GraphData,
    densityCondition G →
      ∃ H : GraphData,
        isCompleteBipartite H ∧
          H.n = G.n ∧
            H.k = G.k ∧
              densityCondition H ∧
                minimizesFor H G

def erdosProblem65 : Prop :=
  erdosLowerBound ∧ completeBipartiteMinimizer

theorem witness_pos :
    claimAt
      { n := 1
        edges := ∅
        k := 0
        cycleLengths := ∅ } := by
  constructor
  · simp [densityCondition, edgeCount]
  · norm_num [lowerBoundCondition, reciprocalCycleSum, Nat.log]

theorem witness_neg :
    ¬ claimAt
      { n := 3
        edges := Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 ≠ p.2)
        k := 2
        cycleLengths := ∅ } := by
  intro h
  rcases h with ⟨_, hlow⟩
  norm_num [lowerBoundCondition, reciprocalCycleSum, Nat.log] at hlow

theorem erdos_65 : erdosProblem65 := by
  sorry

end