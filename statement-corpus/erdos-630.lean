/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
The list chromatic number $\chi_L(G)$ is defined to be the minimal $k$ such that for any assignment of a list of $k$ colours to each vertex of $G$ (perhaps different lists for different vertices) a colouring of each vertex by a colour on its list can be chosen such that adjacent vertices receive distinct colours. Does every planar bipartite graph $G$ have $\chi_L(G)\leq 3$?

NODE n001-resolution (resolution), VERBATIM:
#630 : [ERT80] graph theory | chromatic number A problem of Erdős, Rubin, and Taylor [ERT80] . The answer is yes, proved by Alon and Tarsi [AlTa92] . See also [631] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #630, https://www.erdosproblems.com/630, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable JoshuaB Working on formalising None Previous Next
-/






import Mathlib
open Classical

-- @category research solved





open Classical Filter

namespace Erdos630

/-- A straight-line segment between two points in the Euclidean plane. -/
def Segment (p q : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = t • p + (1 - t) • q}

/-- A finite simple graph is planar when it has a crossing-free straight-line drawing
in the Euclidean plane.  The condition says that distinct edges intersect only at
their common endpoints. -/
def IsPlanarStraight (G : SimpleGraph V) [Fintype V] : Prop :=
  ∃ p : V → EuclideanSpace ℝ (Fin 2),
    Function.Injective p ∧
      ∀ a b c d : V,
        G.Adj a b →
        G.Adj c d →
        ¬ (a = c ∧ b = d) →
        ¬ (a = d ∧ b = c) →
        ∀ x,
          x ∈ Segment (p a) (p b) →
          x ∈ Segment (p c) (p d) →
          x = p a ∨ x = p b ∨ x = p c ∨ x = p d

/-- A graph is bipartite when its vertices admit a two-colouring separating
the endpoints of every edge. -/
def IsBipartite (G : SimpleGraph V) : Prop :=
  ∃ colour : V → Bool, ∀ ⦃u v : V⦄, G.Adj u v → colour u ≠ colour v

/-- `ListColorableAt G k` means that every assignment of finite lists of exactly
`k` colours admits a proper colouring from those lists. -/
def ListColorableAt (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (C : Type) (L : V → Finset C),
    (∀ v, (L v).card = k) →
      ∃ f : V → C,
        (∀ v, f v ∈ L v) ∧
          (∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v)

/-- The set of admissible list sizes for a graph. -/
def ListChromaticSet (G : SimpleGraph V) : Set ℕ :=
  {k | ListColorableAt G k}

/-- The list chromatic number, defined as the infimum of the admissible list
sizes.  The accompanying question below explicitly requires nonemptiness and
boundedness of this set, so the default value of `sInf` on an empty set is not
being used. -/
noncomputable def listChromaticNumber (G : SimpleGraph V) : ℕ :=
  sInf (ListChromaticSet G)

/-- The admissible list-size set is bounded below for every graph; this records
the boundedness side condition needed when using `sInf`. -/
theorem listChromaticSet_bddBelow (G : SimpleGraph V) :
    BddBelow (ListChromaticSet G) := by
  refine ⟨0, ?_⟩
  intro k hk
  exact Nat.zero_le k

/-- A proved control showing that the list-colouring predicate is not a mere
tag: the graph on the empty vertex type is list-colourable from empty lists. -/
theorem empty_listColorableAt_zero :
    ListColorableAt (V := Empty) (⊥ : SimpleGraph Empty) 0 := by
  intro C L hL
  refine ⟨fun v => nomatch v, ?_, ?_⟩
  · intro v
    exact nomatch v
  · intro u v huv
    exact nomatch u

/-- The formalized affirmative answer to Erdős problem 630.  The source asks:
“Does every planar bipartite graph `G` have `χ_L(G) ≤ 3`?”  Here `G` is a finite
simple graph, `IsPlanarStraight G` supplies the planar drawing, and
`IsBipartite G` supplies the two-colouring.  The `sInf` value is accompanied by
the required nonemptiness and bounded-below conditions, avoiding its junk value
on an empty set.  The mathematical proof of the Alon--Tarsi result remains to
be supplied. -/
theorem planar_bipartite_listChromaticNumber_le_three :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsPlanarStraight G →
      IsBipartite G →
      (ListChromaticSet G).Nonempty ∧
        BddBelow (ListChromaticSet G) ∧
        listChromaticNumber G ≤ 3 := by
  sorry Erdos630
