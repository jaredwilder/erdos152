/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
A graph is $(a,b)$-choosable if for any assignment of a list of $a$ colours to each of its vertices there is a subset of $b$ colours from each list such that the subsets of adjacent vertices are disjoint. If $G$ is $(a,b)$-choosable then $G$ is $(am,bm)$-choosable for every integer $m\geq 1$.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#632 : [ERT80] graph theory | chromatic number A problem of Erdős, Rubin, and Taylor [ERT80] . Note that $G$ is $(a,1)$-choosable corresponds to being $a$-choosable, that is, the list chromatic number satisfies $\chi_L(G)\leq a$. This is false: Dvořák, Hu, and Sereni [DHS19] construct a graph which is $(4,1)$-choosable but not $(8,2)$-choosable. See also the entry in the graphs problem collection . Additional thanks to : David Penman and Raphael Steiner Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #632, https://www.erdosproblems.com/632, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/



import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos632

/-- A graph is `(a,b)`-choosable when every assignment of `a`-element
lists of natural-number colours admits `b`-element sublists that are
disjoint on adjacent vertices. -/
def IsChoosable {V : Type} (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ L : V → Finset ℕ,
    (∀ v, (L v).card = a) →
      ∃ S : V → Finset ℕ,
        (∀ v, S v ⊆ L v ∧ (S v).card = b) ∧
          ∀ ⦃u v : V⦄, G.Adj u v → Disjoint (S u) (S v)

/-- The questioned scaling assertion for fixed parameters `(a,b)`: every
`(a,b)`-choosable graph is `(am,bm)`-choosable for every integer `m ≥ 1`. -/
def ScalingStatement (a b : ℕ) : Prop :=
  ∀ {V : Type} (G : SimpleGraph V),
    IsChoosable G a b →
      ∀ m : ℕ, 1 ≤ m → IsChoosable G (a * m) (b * m)

/-- A finite graph counterexample of the type recorded in the resolution:
it is `(4,1)`-choosable but not `(8,2)`-choosable. The construction from
Dvořák, Hu, and Sereni remains to be formalized here. -/
def DHS19Counterexample : Prop :=
  ∃ (V : Type) (_ : Fintype V),
    ∃ G : SimpleGraph V, IsChoosable G 4 1 ∧ ¬ IsChoosable G 8 2

/-- Proved control: on the empty vertex type, the choosability predicate is
satisfied for every graph and every pair of parameters, since all vertexwise
and adjacency requirements are vacuous. -/
theorem empty_vertex_choosable (a b : ℕ) (G : SimpleGraph Empty) :
    IsChoosable G a b := by
  intro L hL
  refine ⟨fun v => nomatch v, ?_, ?_⟩
  · intro v
    exact nomatch v
  · intro u v huv
    exact nomatch u

/-- The resolved counterexample recorded by the source. This is an explicit
named hypothesis for the literature construction; its proof is not supplied
by the source formalization. -/
theorem known_DHS19_counterexample : DHS19Counterexample := by
  sorry

/-- The universal scaling statement is false. Applying it with `m = 2` to the
known `(4,1)`-choosable but not `(8,2)`-choosable graph contradicts the
second conjunct of the counterexample. -/
theorem scaling_statement_false : ¬ ScalingStatement 4 1 := by
  intro h
  rcases known_DHS19_counterexample with ⟨V, hV, G, h41, h82⟩
  have hs : IsChoosable G (4 * 2) (1 * 2) :=
    h G h41 2 (by decide)
  norm_num at hs
  exact h82 hs

#print axioms empty_vertex_choosable
#print axioms scaling_statement_false

end Erdos632
