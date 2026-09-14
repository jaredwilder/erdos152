/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $r,k\geq 2$ be fixed. Let $A\subset \mathbb{R}^2$ be a set of $n$ points with no $k$ points on a line. Determine the threshold $f_{r,k}(n)$ such that if there are at least $f_{r,k}(n)$ many ordinary lines (lines containing exactly two points) then there is a set $A'\subseteq A$ of $r$ points such that all $\binom{r}{2}$ many lines determined by $A'$ are ordinary. Is it true that $f_{r,k}(n)=o(n^2)$, or perhaps even $\ll n$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#960 : [Er84,p.102] geometry Turán's theorem implies\[f_{r,k}(n) \leq \left(1-\frac{1}{r-1}\right)\frac{n^2}{2}+1.\]An internal OpenAI model (see [APSSV26b] ) has shown that in fact for any $r\geq 3$ and $k\geq 4$\[f_{r,k}(n) \geq \frac{n^2}{12}-O(n).\]See also [209] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 09 April 2026. ( View history ) The source records bounds but leaves the threshold question open.
-/






import Mathlib
open Classical

-- @category research open






open Classical Filter

namespace Erdos960

/-- Three points in the Euclidean plane are collinear, expressed using their two coordinates. -/
def Collinear3 (p q r : EuclideanSpace ℝ (Fin 2)) : Prop :=
  (q 0 - p 0) * (r 1 - p 1) = (q 1 - p 1) * (r 0 - p 0)

/-- A pair of indexed points determines an ordinary line when no other indexed point
lies on the line through the pair. -/
def IsOrdinaryPair {n : ℕ} (A : Fin n → EuclideanSpace ℝ (Fin 2))
    (i j : Fin n) : Prop :=
  i ≠ j ∧ ∀ l, l ≠ i → l ≠ j → ¬ Collinear3 (A i) (A j) (A l)

/-- A finite point configuration has no k points on one line. -/
def HasNoKCollinear {n k : ℕ} (A : Fin n → EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∀ S : Finset (Fin n), S.card = k →
    ¬ ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ ∀ l ∈ S, Collinear3 (A i) (A j) (A l)

/-- The number of ordinary lines, represented uniquely by their increasing pair of endpoints. -/
def OrdinaryLineCount {n : ℕ} (A : Fin n → EuclideanSpace ℝ (Fin 2)) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ IsOrdinaryPair A p.1 p.2)).card

/-- A configuration contains r points whose every joining line is ordinary. -/
def HasOrdinaryRSet {n r : ℕ} (A : Fin n → EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ S : Finset (Fin n), S.card = r ∧
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsOrdinaryPair A i j

/-- The literal threshold property asked for by the source, including minimality of the
candidate threshold. The use of a threshold is a lower-bound implication, so no supremum
or infimum junk is involved. -/
def ThresholdSpec (r k n f : ℕ) : Prop :=
  (∀ A : Fin n → EuclideanSpace ℝ (Fin 2),
      HasNoKCollinear A →
      f ≤ OrdinaryLineCount A →
      HasOrdinaryRSet A) ∧
  (∀ g < f, ∃ A : Fin n → EuclideanSpace ℝ (Fin 2),
      HasNoKCollinear A ∧ g ≤ OrdinaryLineCount A ∧ ¬ HasOrdinaryRSet A)

/-- The unresolved question of determining the threshold f_{r,k}(n). -/
def ThresholdQuestion (r k n : ℕ) : Prop :=
  2 ≤ r ∧ 2 ≤ k ∧ ∃ f, ThresholdSpec r k n f

/-- A finite lattice point configuration used to provide decidable controls for the
geometric predicates. Coordinates are natural numbers below m, so every quantifier
in the definition is over a finite decidable type. -/
abbrev LatticeConfiguration (n m : ℕ) := Fin n → Fin 2 → Fin m

/-- Collinearity for three finite lattice points, computed by an integer determinant. -/
def LatticeCollinear3 {n m : ℕ} (A : LatticeConfiguration n m)
    (i j l : Fin n) : Prop :=
  (((A j 0).val : ℤ) - (A i 0).val) * (((A l 1).val : ℤ) - (A i 1).val) =
    (((A j 1).val : ℤ) - (A i 1).val) * (((A l 0).val : ℤ) - (A i 0).val)

/-- The finite analogue of an ordinary line. -/
def LatticeOrdinaryPair {n m : ℕ} (A : LatticeConfiguration n m)
    (i j : Fin n) : Prop :=
  i ≠ j ∧ ∀ l, l ≠ i → l ≠ j → ¬ LatticeCollinear3 A i j l

/-- The finite analogue of having no k points on a line. -/
def LatticeHasNoKCollinear {n m k : ℕ} (A : LatticeConfiguration n m) : Prop :=
  ∀ S : Finset (Fin n), S.card = k →
    ¬ ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ ∀ l ∈ S, LatticeCollinear3 A i j l

/-- The finite analogue of containing an r-set all of whose joining lines are ordinary. -/
def LatticeHasOrdinaryRSet {n m r : ℕ} (A : LatticeConfiguration n m) : Prop :=
  ∃ S : Finset (Fin n), S.card = r ∧
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j → LatticeOrdinaryPair A i j

/-- The decidable bounded-instance predicate used for concrete positive and negative
witnesses. It records the parameter restrictions, the no-k-collinear condition, and
the desired ordinary r-point configuration. -/
def DFinite (n m r k : ℕ) (A : LatticeConfiguration n m) : Prop :=
  2 ≤ r ∧ 2 ≤ k ∧ LatticeHasNoKCollinear A ∧ LatticeHasOrdinaryRSet A

/-- POSITIVE WITNESS: three lattice points, no three collinear, with an ordinary pair-set. -/
def Apos : LatticeConfiguration 3 4 :=
  ![![0, 0], ![1, 0], ![0, 1]]

/-- NEGATIVE WITNESS: the near-miss obtained by moving the third point onto the line
through the first two, thereby breaking exactly the no-three-collinear condition. -/
def Aneg : LatticeConfiguration 3 4 :=
  ![![0, 0], ![1, 0], ![2, 0]]

/-- POSITIVE WITNESS: the concrete noncollinear configuration satisfies the finite predicate. -/
theorem DFinite_witness_pos :
    DFinite 3 4 2 3 Apos := by
  decide

/-- NEGATIVE WITNESS: the near-miss configuration fails the finite predicate. -/
theorem DFinite_witness_neg :
    ¬ DFinite 3 4 2 3 Aneg := by
  decide

/-- A proved computational control showing that the finite predicate is not vacuous:
its positive and negative witnesses have opposite truth values. -/
theorem DFinite_witness_separation :
    DFinite 3 4 2 3 Apos ∧ ¬ DFinite 3 4 2 3 Aneg := by
  exact ⟨DFinite_witness_pos, DFinite_witness_neg⟩

end Erdos960
