/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $1\leq k<n$. Given $n$ points in $\mathbb{R}^2$, at most $n-k$ on any line, there are $\gg kn$ many lines which contain at least two points.
-/

/- 
SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#211 : [Er75f,p.105] [Er81] [Er83c] [Er84] geometry In particular, given any $2n$ points with at most $n$ on a line there are $\gg n^2$ many lines formed by the points. Solved by Beck [Be83] and Szemerédi and Trotter [SzTr83] . In [Er84] Erdős speculates that perhaps there are $\geq (1+o(1))kn/6$ many such lines, but says 'perhaps [this] is too optimistic and one should first look for a counterexample'. The constant $1/6$ would be best possible here, since there are arrangements of $n$ points with no four points on a line and $\sim n^2/6$ many lines containing three points (see Burr, Grünbaum, and Sloane [BGS74] and Füredi and Palásti [FuPa84] ). Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links This page was last edited 16 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #211, https://www.erdosproblems.com/211, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

import Mathlib

-- @category research solved

namespace Erdos211

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A parametrized affine line in the Euclidean plane through two points. -/
def affineLineThrough (p q : Plane) : Set Plane :=
  {x | ∃ t : ℝ, x = p + t • (q - p)}

/-- The finite type of ordered pairs of distinct point indices, written in increasing order. -/
def PairIndex (n : ℕ) :=
  {ij : Fin n × Fin n // ij.1 < ij.2}

/-- Two index pairs represent the same geometric line when their parametrized lines agree. -/
def pairSetoid {n : ℕ} (P : Fin n → Plane) : Setoid (PairIndex n) where
  r a b := affineLineThrough (P a.1.1) (P a.1.2) =
    affineLineThrough (P b.1.1) (P b.1.2)
  iseqv := by
    constructor
    · intro a
      rfl
    · intro a b h
      exact h.symm
    · intro a b c h₁ h₂
      exact h₁.trans h₂

/-- The number of distinct lines determined by pairs of the given finite point configuration. -/
noncomputable def lineCount (P : Fin n → Plane) : ℕ :=
  letI := Fintype.ofFinite (Quotient (pairSetoid P))
  Fintype.card (Quotient (pairSetoid P))

/-- The number of points of a configuration lying on a specified set. -/
def pointsOn (P : Fin n → Plane) (L : Set Plane) : ℕ :=
  (Finset.univ.filter (fun i => P i ∈ L)).card

/-- A set is an affine line when it is a nonconstant affine parametrization. -/
def IsAffineLine (L : Set Plane) : Prop :=
  ∃ p v : Plane, v ≠ 0 ∧ L = {x | ∃ t : ℝ, x = p + t • v}

/-- The hypothesis that every affine line contains at most `n-k` points. -/
def AtMostOnLine (P : Fin n → Plane) (k : ℕ) : Prop :=
  ∀ L : Set Plane, IsAffineLine L → pointsOn P L ≤ n - k

/-- There are at least a positive constant multiple of `k*n` determined lines. -/
def ManyLines (P : Fin n → Plane) (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    c * (k : ℝ) * (n : ℝ) ≤ (lineCount P : ℝ)

/-- The literal formalization of the question, with distinct points made explicit. -/
def BeckQuestion : Prop :=
  ∀ (n k : ℕ) (P : Fin n → Plane),
    1 ≤ k → k < n → Function.Injective P →
      AtMostOnLine P k → ManyLines P k

/-- The resolved special case recorded in the source for `2n` points. -/
def BeckTwoNQuestion : Prop :=
  ∀ (n : ℕ) (P : Fin (2 * n) → Plane),
    Function.Injective P →
      AtMostOnLine P n → ManyLines P n

/-- The source says that the general assertion and its `2n` special case are solved by the cited results. -/
def ResolvedByBeckAndSzemerediTrotter : Prop :=
  BeckQuestion ∧ BeckTwoNQuestion

/-- Every point lies on the parametrized affine line through that point and any second point. -/
theorem point_mem_affineLineThrough (p q : Plane) :
    p ∈ affineLineThrough p q := by
  refine ⟨0, ?_⟩
  simp

/-- Equality of parametrized lines is reflexive, providing a consistency control for the line quotient. -/
theorem pairSetoid_refl {n : ℕ} (P : Fin n → Plane) (a : PairIndex n) :
    (pairSetoid P).r a a := by
  rfl

#print axioms point_mem_affineLineThrough
#print axioms pairSetoid_refl

end Erdos211