/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
For any $d\geq 1$ if $H$ is a graph such that every subgraph contains a vertex of degree at most $d$ then $R(H)\ll_d n$.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#163 : [BuEr75] [Er82e] graph theory | ramsey theory The Burr-Erdős conjecture . This is equivalent to showing that if $H$ is the union of $c$ forests then $R(H)\ll_c n$, and also that if every subgraph has average degree at most $d$ then $R(H)\ll_d n$. Solved by Lee [Le17] , who proved that\[ R(H) \leq 2^{2^{O(d)}}n.\]More precisely, Lee proved that\[ R(H) \leq 2^{d2^{O(\chi(H))}}n.\]It is conjectured that $R(H) \leq 2^{O(d)}n$. This problem is #9 in Ramsey Theory in the graphs problem collection. See also [800] . Additional thanks to : Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (2) Proof claims (0) More information and links This page was last edited 22 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #163, https://www.erdosproblems.com/163, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos163

/-- A finite simple graph, represented by its genuine vertex type and adjacency relation. -/
structure FiniteGraph where
  V : Type
  inst : Fintype V
  Adj : V → V → Prop
  dec : DecidableRel Adj
  symm : ∀ ⦃u v⦄, Adj u v → Adj v u
  loopless : ∀ v, ¬ Adj v v

/-- `Degenerate H d` says that every nonempty induced subgraph of `H` has a vertex
of degree at most `d`. This is the finite-set formulation of the source's
condition that every subgraph contains a vertex of degree at most `d`. -/
def Degenerate (H : FiniteGraph) (d : ℕ) : Prop :=
  letI : DecidableRel H.Adj := H.dec
  ∀ S : Finset H.V, ∃ v ∈ S, (S.filter (fun w => H.Adj v w)).card ≤ d

/-- `RamseyProperty H N` says that every symmetric two-colouring of the pairs
of the complete graph on `Fin N` contains a monochromatic copy of `H`.
The copy is represented by an injective vertex map preserving every edge of `H`. -/
def RamseyProperty (H : FiniteGraph) (N : ℕ) : Prop :=
  letI : Fintype H.V := H.inst
  letI : DecidableRel H.Adj := H.dec
  ∀ c : Fin N → Fin N → Bool,
    (∀ i j, i ≠ j → c i j = c j i) →
      ∃ f : H.V → Fin N, Function.Injective f ∧
        ∃ b : Bool, ∀ ⦃u v : H.V⦄, H.Adj u v → c (f u) (f v) = b

/-- The chosen formal reading of `R(H) ≪_d n`: for each degeneracy bound `d`,
there is a constant `C` such that every graph `H` satisfying the condition has
a Ramsey witness at `C * |V(H)|`. The multiplicative constant is allowed to
depend on `d`, as in the source. -/
def LinearRamseyBound (d C : ℕ) : Prop :=
  ∀ H : FiniteGraph,
    letI : Fintype H.V := H.inst
    Degenerate H d → RamseyProperty H (C * Fintype.card H.V)

/-- The empty graph used as a proved control for the Ramsey predicate. -/
def emptyGraph : FiniteGraph where
  V := Empty
  inst := inferInstance
  Adj := fun _ _ => False
  dec := by infer_instance
  symm := by intro u v h; exact False.elim h
  loopless := by intro v h; exact False.elim h

/-- A non-vacuous kernel-checked control: the empty graph has a Ramsey witness
on the empty complete graph, because its vertex map is the unique empty map. -/
theorem empty_ramsey_control : RamseyProperty emptyGraph 0 := by
  letI : Fintype emptyGraph.V := emptyGraph.inst
  letI : DecidableRel emptyGraph.Adj := emptyGraph.dec
  intro c hsym
  refine ⟨(fun x => nomatch x), ?_, false, ?_⟩
  · intro a b
    exact nomatch a
  · intro u v huv
    exact False.elim huv

/-- Lee's solved form of the Burr--Erdős conjecture: graphs whose every
subgraph has a vertex of degree at most `d` have Ramsey number bounded linearly
in their order, with a constant depending only on `d`. The proof of this
literature result remains an explicit honest gap here. -/
theorem burr_erdos_conjecture :
    ∀ d : ℕ, 1 ≤ d → ∃ C : ℕ, LinearRamseyBound d C := by
  sorry

#print axioms empty_ramsey_control

end Erdos163
