/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Does there exist $S\subseteq \mathbb{R}^2$ such that every set congruent to $S$ (that is, $S$ after some translation and rotation) contains exactly one point from $\mathbb{Z}^2$?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#215 : [Er83c] geometry An old question of Steinhaus. Erdős was 'almost certain that such a set does not exist'. In fact, such a set does exist, as proved by Jackson and Mauldin [JaMa02] . Their construction depends on the axiom of choice. Additional thanks to : Vjekoslav Kovac Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Formalised statement? No ( create one )
-/





-- @category research solved

import Mathlib
open Classical






open Classical Filter

namespace Erdos215

/-- The Euclidean plane, represented with the Euclidean metric rather than the
sup metric on a product. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Rotation through angle `θ` about the origin, written in coordinates on
`EuclideanSpace ℝ (Fin 2)`. -/
def rotate (θ : ℝ) (x : Plane) : Plane :=
  ![Real.cos θ * x 0 - Real.sin θ * x 1,
    Real.sin θ * x 0 + Real.cos θ * x 1]

/-- A point of the Euclidean plane is a lattice point when each of its two
coordinates is an integer. -/
def IsLatticePoint (x : Plane) : Prop :=
  ∀ i : Fin 2, ∃ n : ℤ, x i = (n : ℝ)

/-- `IsCongruent S T` means that `T` is obtained from `S` by one rotation
about the origin followed by one translation. Thus `S` is the original set
and `T` is its congruent image. -/
def IsCongruent (S T : Set Plane) : Prop :=
  ∃ θ : ℝ, ∃ t : Plane, T = (fun x => rotate θ x + t) '' S

/-- A set contains exactly one lattice point. -/
def ExactlyOneLattice (S : Set Plane) : Prop :=
  ∃! z : Plane, z ∈ S ∧ IsLatticePoint z

/-- The source's property for a set `S`: every rotated and translated image
contains exactly one point of `ℤ²`. -/
def HasSteinhausProperty (S : Set Plane) : Prop :=
  ∀ T : Set Plane, IsCongruent S T → ExactlyOneLattice T

/-- The literal formalization of the source question. The resolution records
that this proposition is true, by the construction of Jackson and Mauldin;
the construction and its use of choice remain to be formalized here. -/
def SteinhausQuestion : Prop :=
  ∃ S : Set Plane, HasSteinhausProperty S

/-- The zero point is a lattice point. This is a proved control showing that
`IsLatticePoint` is not an empty or vacuous predicate. -/
theorem lattice_zero : IsLatticePoint (0 : Plane) := by
  intro i
  exact ⟨0, by simp⟩

/-- The singleton `{0}` contains exactly one lattice point. This is a proved
control exercising the definition of `ExactlyOneLattice`. -/
theorem singleton_control : ExactlyOneLattice ({0} : Set Plane) := by
  refine ⟨0, ⟨by simp, lattice_zero⟩, ?_⟩
  intro y hy
  exact Set.mem_singleton_iff.mp hy.1

/-- Jackson and Mauldin's existence theorem answering the source question.
The mathematical construction of the required set is not reproduced here. -/
theorem jackson_mauldin_existence : SteinhausQuestion := by
  sorry

#print axioms singleton_control

end Erdos215
