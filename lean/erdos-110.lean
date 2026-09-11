import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
universe u v

namespace ErdosProblem110

structure Graph where
  V : Type u
  Adj : V → V → Prop
  symm : ∀ {x y}, Adj x y → Adj y x
  loopless : ∀ x, ¬ Adj x x

def Colorable (G : Graph.{u}) (α : Type v) : Prop :=
  ∃ f : G.V → α, ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y

def ChromaticAlephOne (G : Graph.{u}) : Prop :=
  ∃ α : Type u,
    Cardinal.mk α = Cardinal.aleph 1 ∧
      Colorable G α ∧
        ∀ β : Type u,
          Cardinal.mk β < Cardinal.aleph 1 → ¬ Colorable G β

structure Subgraph (G : Graph.{u}) where
  carrier : Finset G.V
  Adj : {x // x ∈ carrier} → {x // x ∈ carrier} → Prop
  symm : ∀ {x y}, Adj x y → Adj y x
  loopless : ∀ x, ¬ Adj x x
  le_adj : ∀ {x y}, Adj x y → G.Adj x.1 y.1

def Subgraph.toGraph {G : Graph.{u}} (H : Subgraph G) : Graph.{u} where
  V := {x // x ∈ H.carrier}
  Adj := H.Adj
  symm := H.symm
  loopless := H.loopless

def HasChromaticNumber (G : Graph.{u}) (n : ℕ) : Prop :=
  Colorable G (Fin n) ∧ ¬ Colorable G (Fin (n - 1))

theorem erdosProblem110 :
    ∃ F : ℕ → ℕ,
      ∀ᶠ n in Filter.atTop,
        ∀ G : Graph.{u},
          ChromaticAlephOne G →
            ∃ H : Subgraph G,
              H.carrier.card ≤ F n ∧
                HasChromaticNumber H.toGraph n := by
  sorry

end ErdosProblem110

end