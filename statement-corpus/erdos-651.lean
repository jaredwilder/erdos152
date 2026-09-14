/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f_k(n)$ denote the smallest integer such that any $f_k(n)$ points in general position in $\mathbb{R}^k$ contain $n$ which determine a convex polyhedron. Is it true that\[f_k(n) > (1+c_k)^n\]for some constant $c_k>0$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#651 : [Er97e] geometry | convex The function when $k=2$ is the subject of the Erdős-Klein-Szekeres conjecture, see [107] . One can show that\[f_2(n)>f_3(n)>\cdots.\]The answer is no, even for $k=3$: Pohoata and Zakharov [PoZa22] have proved that\[f_3(n)\leq 2^{o(n)}.\] Additional thanks to : Mehtaab Sawhney Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (3) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #651, https://www.erdosproblems.com/651, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


-- @category research solved

import Mathlib
open Classical
open Filter








open Classical Filter

namespace Erdos651

/-- The Euclidean ambient space corresponding to `ℝ^k` in the source. -/
abbrev Ambient (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- A finite set of points is in general position when every nonempty subset of
cardinality at most `k + 1` is affinely independent. -/
def InGeneralPosition (k : ℕ) (S : Finset (Ambient k)) : Prop :=
  ∀ T : Finset (Ambient k), T ⊆ S → T.card ≤ k + 1 → T.Nonempty →
    AffineIndependent ℝ (fun i : T => (i : Ambient k))

/-- A proved sanity control: the empty configuration is in general position.
This exercises the formalized predicate rather than an unrelated arithmetic fact. -/
theorem empty_is_generalPosition (k : ℕ) :
    InGeneralPosition k (∅ : Finset (Ambient k)) := by
  intro T hT _ hne
  have hTempty : T = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    exact (Finset.not_mem_empty x) (hT hx)
  exfalso
  simpa [hTempty] using hne

/-- `DeterminesConvexPolyhedron` records the geometric condition that the selected
points determine a convex polyhedron. Its precise polyhedral and vertex-level
formalization remains an explicit gap in this artifact rather than being replaced
by a tag or an unrelated predicate. -/
def DeterminesConvexPolyhedron {k : ℕ} (S : Finset (Ambient k)) : Prop := by
  sorry

/-- The admissible cardinalities in the literal definition of `f_k(n)`. -/
def AdmissibleCardinalities (k n : ℕ) : Set ℕ :=
  {m | ∀ S : Finset (Ambient k), S.card = m →
    InGeneralPosition k S →
    ∃ T : Finset (Ambient k), T ⊆ S ∧ T.card = n ∧
      DeterminesConvexPolyhedron T}

/-- The source's smallest-integer function, represented by `sInf`.
This is an `sInf` definition, so its intended mathematical use requires the
admissible set to be nonempty and bounded above; those conditions are not
silently inferred from Lean's junk value for an empty or unbounded `sInf`. -/
noncomputable def f (k n : ℕ) : ℕ :=
  sInf (AdmissibleCardinalities k n)

/-- The exponential lower-bound assertion asked for in the source, at a fixed
dimension `k`. The natural number `f k n` is coerced to `ℝ` for comparison. -/
def ExponentialLowerBoundAt (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, (f k n : ℝ) > (1 + c) ^ n

/-- The recorded resolution says that the exponential lower bound fails already
in dimension three. The proof of the Pohoata--Zakharov subexponential estimate
and the missing exact polyhedral predicate are not reproved here. -/
theorem no_exponential_lower_bound_in_dimension_three :
    ¬ ExponentialLowerBoundAt 3 := by
  sorry

#print axioms empty_is_generalPosition

end Erdos651
