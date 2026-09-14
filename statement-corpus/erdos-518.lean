/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is it true that, in any two-colouring of the edges of $K_n$, there exist $\sqrt{n}$ monochromatic paths, all of the same colour, which cover all vertices?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#518 : [ErGy95] graph theory | ramsey theory A problem of Erdős and Gyárfás. Gerencsér and Gyárfás [GeGy67] proved that, if the paths do not need to be of the same colour, then two paths suffice. Erdős and Gyárfás [ErGy95] proved that $2\sqrt{n}$ vertices suffice, and observed that $\sqrt{n}$ would be best possible here. Solved in the affirmative by Pokrovskiy, Versteegen, and Williams [PVW24] . Additional thanks to : Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (1) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #518, https://www.erdosproblems.com/518, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/






import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos518

/-- A two-colouring of the edges of the complete graph on `Fin n`, represented by
a symmetric colour function. The two colours are the elements of `Fin 2`. -/
structure EdgeColoring (n : ℕ) where
  color : Fin n → Fin n → Fin 2
  symm : ∀ x y, color x y = color y x

/-- The complete graph on the vertex type `Fin n`. -/
def completeGraph (n : ℕ) : SimpleGraph (Fin n) := ⊤

/-- The recursive condition that a nonempty list is a path whose consecutive
edges all have the specified colour in a given edge-colouring. -/
def MonoPath {n : ℕ} (c : EdgeColoring n) (col : Fin 2) :
    List (Fin n) → Prop
  | [] => False
  | _ :: [] => True
  | a :: b :: xs =>
      ((completeGraph n).Adj a b) ∧ c.color a b = col ∧
        MonoPath c col (b :: xs)

/-- A family of vertex-disjointness is not required here: the source only asks
that the paths cover all vertices. This predicate says that every vertex lies
on at least one member of the family. -/
def Covers {n : ℕ} (family : Finset (List (Fin n))) : Prop :=
  ∀ v : Fin n, ∃ p ∈ family, v ∈ p

/-- Every member of the family is a simple monochromatic path of one common
colour. Simplicity is expressed by `List.Nodup`. -/
def IsMonoPathFamily {n : ℕ} (c : EdgeColoring n)
    (family : Finset (List (Fin n))) (col : Fin 2) : Prop :=
  ∀ p ∈ family, p.Nodup ∧ MonoPath c col p

/-- The complete graph has an edge between any two distinct vertices. This is
a proved control for the graph and adjacency conventions used in the
formalization. -/
theorem completeGraph_adj_control (n : ℕ) (x y : Fin n) (hxy : x ≠ y) :
    (completeGraph n).Adj x y := by
  simp [completeGraph, hxy]

/-- A one-vertex instance has a covering monochromatic path family. This
proved control checks that the path, colour, and covering predicates are not
vacuous. -/
theorem one_vertex_control :
    ∃ (c : EdgeColoring 1) (family : Finset (List (Fin 1))),
      family.card ≤ Nat.sqrt 1 ∧
      ∃ col : Fin 2,
        IsMonoPathFamily c family col ∧ Covers family := by
  let c : EdgeColoring 1 :=
    { color := fun _ _ => 0
      symm := by intros x y; rfl }
  refine ⟨c, {[(0 : Fin 1)]}, ?_, 0, ?_, ?_⟩
  · simp
  · intro p hp
    have hp' : p = [(0 : Fin 1)] := by
      simpa using hp
    subst p
    simp [IsMonoPathFamily, MonoPath, completeGraph]
  · intro v
    have hv : v = (0 : Fin 1) := Fin.eq_zero v
    subst v
    exact ⟨[(0 : Fin 1)], by simp, by simp⟩

/-- Formalization of Erdos problem 518.

The source sentence says that for every two-colouring of the edges of `K_n`,
there are `sqrt n` monochromatic paths, all of one colour, covering every
vertex. We formalize “there exist `sqrt n` paths” in the usual upper-bound
sense as a family of at most `Nat.sqrt n` paths; singleton paths are allowed,
and paths need not be disjoint because the source only requires coverage.

The affirmative result is recorded in the source as solved by Pokrovskiy,
Versteegen, and Williams [PVW24]. The remaining gap is the proof of this
general theorem from the cited result. -/
theorem monochromatic_path_cover :
    ∀ n : ℕ, ∀ c : EdgeColoring n,
      ∃ family : Finset (List (Fin n)),
        family.card ≤ Nat.sqrt n ∧
        ∃ col : Fin 2,
          IsMonoPathFamily c family col ∧ Covers family := by
  sorry

#print axioms monochromatic_path_cover

end Erdos518
