
import Mathlib
open scoped EuclideanSpace

/-
SOURCE (frozen), node `n000-question`, VERBATIM:
For a set of $n$ points $P\subset \mathbb{R}^2$ let $\ell_1,\ldots,\ell_m$ be the lines determined by $P$, and let $A=\{\lvert \ell_1\cap P\rvert,\ldots,\lvert \ell_m\cap P\rvert\}$. Let $F(n)$ count the number of possible sets $A$ that can be constructed this way. Is it true that\[F(n) \leq \exp(O(\sqrt{n}))?\]
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#607 : [Er85] geometry Erdős writes it is 'easy to see' that this bound would be best possible. This was proved by Szemerédi and Trotter [SzTr83] . Additional thanks to : Noga Alon Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #607, https://www.erdosproblems.com/607, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

-- @category research open

namespace Erdos607

/-- The Euclidean plane used for the formalization of the source problem. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The affine line through two distinct points of the Euclidean plane. -/
def lineThrough (p q : Plane) : Set Plane :=
  {x | ∃ t : ℝ, x = p + t • (q - p)}

/-- The finite set of lines determined by pairs of distinct points of a finite point set. -/
noncomputable def determinedLines (P : Finset Plane) : Finset (Set Plane) := by
  classical
  exact
    ((P.product P).filter (fun pq => pq.1 ≠ pq.2)).image
      (fun pq => lineThrough pq.1 pq.2)

/-- The set of cardinalities of intersections of the determined lines with the point set. -/
noncomputable def intersectionCardinalities (P : Finset Plane) : Finset ℕ := by
  classical
  exact
    (determinedLines P).image
      (fun L => (P.filter (fun p => p ∈ L)).card)

/-- The collection of all intersection-cardinality sets arising from point sets of size `n`. -/
def possibleCardinalitySets (n : ℕ) : Set (Finset ℕ) :=
  {A | ∃ P : Finset Plane, P.card = n ∧ A = intersectionCardinalities P}

/-- The number of possible intersection-cardinality sets, represented by the cardinality
of the corresponding subtype. -/
noncomputable def F (n : ℕ) : ℕ :=
  Nat.card {A : Finset ℕ // A ∈ possibleCardinalitySets n}

/-- The statement that `F(n)` is bounded by an exponential in the square root of `n`. -/
def Question : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (F n : ℝ) ≤ Real.exp (C * Real.sqrt (n : ℝ))

/-- The empty point set determines no lines and hence has no intersection cardinalities. -/
theorem intersectionCardinalities_empty :
    intersectionCardinalities (∅ : Finset Plane) = ∅ := by
  classical
  simp [intersectionCardinalities, determinedLines]

#print axioms intersectionCardinalities_empty

end Erdos607
