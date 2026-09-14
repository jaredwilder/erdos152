/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f_3(n)$ be the maximal size of a subset of $\{0,1,2\}^n$ which contains no three points on a line. Is it true that $f_3(n)=o(3^n)$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#185 : [Er73] additive combinatorics Originally considered by Moser. It is trivial that $f_3(n)\geq R_3(3^n)$, the maximal size of a subset of $\{1,\ldots,3^n\}$ without a three-term arithmetic progression. Moser showed that\[f_3(n) \gg \frac{3^n}{\sqrt{n}}.\]The answer is yes, which is a corollary of the density Hales-Jewett theorem, proved by Furstenberg and Katznelson [FuKa91] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #185, https://www.erdosproblems.com/185, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A003142 Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable Working on formalising None Previous Next
-/





import Mathlib
open Classical
open Filter

-- @category research solved






open Classical Filter

namespace Erdos185

/-- The discrete cube `{0,1,2}^n`, represented as functions from `Fin n` to `Fin 3`. -/
abbrev Point (n : ℕ) := Fin n → Fin 3

/-- The canonical realization of a point of the discrete cube as a vector in Euclidean space. -/
def pointVector {n : ℕ} (p : Point n) : EuclideanSpace ℝ (Fin n) :=
  fun i => (p i : ℝ)

/-- Three distinct cube points are on a common affine line when they have distinct affine
parameters on one line in the ambient Euclidean space. -/
def ThreeOnLine {n : ℕ} (p q r : Point n) : Prop :=
  p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    ∃ (x v : EuclideanSpace ℝ (Fin n)) (a b c : ℝ),
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      pointVector p = x + a • v ∧
      pointVector q = x + b • v ∧
      pointVector r = x + c • v

/-- A finite subset of the discrete cube is admissible when it contains no three points on a line. -/
def Admissible {n : ℕ} (A : Finset (Point n)) : Prop :=
  ∀ ⦃p q r : Point n⦄, p ∈ A → q ∈ A → r ∈ A → ¬ ThreeOnLine p q r

/-- The set of cardinalities of admissible subsets of the discrete cube. -/
def AdmissibleCard (n : ℕ) : Set ℕ :=
  {k | ∃ A : Finset (Point n), A.card = k ∧ Admissible A}

/-- The maximal size of a subset of `{0,1,2}^n` containing no three points on a line.
The `sSup` is safe here: the admissible cardinalities are nonempty and bounded above, as
proved below, so neither the empty-set nor unbounded-set default value is being used. -/
noncomputable def f3 (n : ℕ) : ℕ :=
  sSup (AdmissibleCard n)

/-- The empty subset witnesses that the set of admissible cardinalities is nonempty. -/
theorem admissibleCard_nonempty (n : ℕ) : (AdmissibleCard n).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨∅, by simp, ?_⟩
  intro p q r hp
  simp at hp

/-- Every admissible cardinality is at most the cardinality of the whole discrete cube. -/
theorem admissibleCard_bddAbove (n : ℕ) : BddAbove (AdmissibleCard n) := by
  refine ⟨Fintype.card (Point n), ?_⟩
  rintro k ⟨A, rfl, hA⟩
  simpa using (Finset.card_le_univ A)

/-- A basic proved control showing that the file's own admissibility predicate is inhabited,
rather than merely introducing an opaque extremal quantity. -/
theorem empty_admissible (n : ℕ) : Admissible (∅ : Finset (Point n)) := by
  intro p q r hp
  simp at hp

/-- The affirmative answer to Erdős problem #185: the maximal progression-free subset of the
ternary discrete cube has density tending to zero. The source sentence reads “Is it true that
`f_3(n)=o(3^n)`?”, and the recorded resolution says “The answer is yes”; this is formalized as
little-o of the real-valued sequence `3^n`. The proof remains a named gap for the density
Hales--Jewett consequence recorded in the source. -/
theorem f3_littleO :
    IsLittleO (fun n : ℕ => (f3 n : ℝ)) (fun n : ℕ => (3 : ℝ) ^ n) atTop := by
  sorry Erdos185
