/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Call a sequence $1< X_1\leq \cdots \leq X_m\leq n$ block-compatible if there is a pairwise balanced block design $A_1,\ldots,A_m\subseteq \{1,\ldots,n\}$ such that $\lvert A_i\rvert=X_i$ for $1\leq i\leq m$. (A pairwise block design means that every pair in $\{1,\ldots,n\}$ is contained in exactly one of the $A_i$.) Are there necessary and sufficient conditions for $(X_i)$ to be block-compatible? Is there some constant $c>0$ such that for all large $n$ there are\[\geq \exp(c n^{1/2}\log n)\]many block-compatible sequences for $\{1,\ldots,n\}$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#732 : [Er81] combinatorics Erdős noted that a trivial necessary condition is $\sum_i \binom{X_i}{2}=\binom{n}{2}$, but wasn't sure if there would be a reasonable necessary and sufficient condition. He could prove that there are\[\leq \exp(O(n^{1/2}\log n))\]many block-compatible sequences for $\{1,\ldots,n\}$. Alon has proved there are at least\[2^{(\frac{1}{2}+o(1))n^{1/2}\log n}\]many sequences which are block-compatible for $n$. See also [733] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Formalised statement? No ( create one )
-/


import Mathlib
open Classical
open Filter
open scoped BigOperators

-- @category research open








open Classical Filter

namespace Erdos732

/-- A pairwise balanced block design on `Fin n`, indexed by `Fin m`: every
distinct pair of points lies in exactly one indexed block. -/
def PairwiseBalanced (n m : ℕ) (A : Fin m → Finset (Fin n)) : Prop :=
  ∀ x y : Fin n, x ≠ y →
    ∃! i : Fin m, x ∈ A i ∧ y ∈ A i

/-- The literal formalization of block-compatibility for a nondecreasing
sequence `X : Fin m → ℕ`. The points are represented by `Fin n`, and the
blocks are indexed by the same finite index type as the sequence. -/
def BlockCompatible (n m : ℕ) (X : Fin m → ℕ) : Prop :=
  (∀ i : Fin m, 1 < X i ∧ X i ≤ n) ∧
    (∀ i j : Fin m, i ≤ j → X i ≤ X j) ∧
    ∃ A : Fin m → Finset (Fin n),
      (∀ i : Fin m, (A i).card = X i) ∧
      PairwiseBalanced n m A

/-- A sequence together with its finite index set. -/
abbrev IndexedSequence := Sigma (fun m : ℕ => Fin m → ℕ)

/-- The predicate that an indexed sequence is block-compatible for `n`. -/
def IsBlockCompatibleSequence (n : ℕ) (s : IndexedSequence) : Prop :=
  BlockCompatible n s.1 s.2

/-- The necessary pair-count condition recorded in the resolution:
the blocks partition the unordered pairs of points. -/
def PairCountCondition (n m : ℕ) (X : Fin m → ℕ) : Prop :=
  ∑ i : Fin m, Nat.choose (X i) 2 = Nat.choose n 2

/-- The pair-count condition is necessary for block-compatibility.
The counting argument relating the unique-pair condition to this equality
remains to be formalized. -/
theorem pair_count_necessary {n m : ℕ} {X : Fin m → ℕ}
    (hX : BlockCompatible n m X) :
    PairCountCondition n m X := by
  sorry

/-- A concrete nondegenerate control: the unique block on two points is a
pairwise balanced design with sequence `(2)`. -/
theorem two_block_control : BlockCompatible 2 1 (fun _ : Fin 1 => 2) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp
  · intro i j hij
    simp
  · refine ⟨fun _ : Fin 1 => (Finset.univ : Finset (Fin 2)), ?_, ?_⟩
    · intro i
      simp
    · intro x y hxy
      refine ⟨0, ?_, ?_⟩
      · simp
      · intro z hz
        exact Fin.eq_zero z

#print axioms two_block_control

/-- The quantitative lower-bound assertion corresponding to Alon's result:
for some positive constant `c`, all sufficiently large `n` admit at least
`exp (c n^(1/2) log n)` distinct block-compatible indexed sequences. The
finite-set formulation avoids assigning a possibly noncomputable cardinality
to the entire class of sequences. This declaration records the literature
result; its proof is not formalized here. -/
def AlonLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in atTop,
      ∃ S : Finset IndexedSequence,
        (∀ s ∈ S, IsBlockCompatibleSequence n s) ∧
          Real.exp (c * (Nat.sqrt n : ℝ) * Real.log (n : ℝ)) ≤
            (S.card : ℝ)

/-- Alon's proved lower bound for the number of block-compatible sequences,
as reported in the resolution of Erdős problem #732. The analytic and
design-theoretic construction supplying this result remains an assumed
literature input in this formalization. -/
theorem alon_lower_bound : AlonLowerBound := by
  sorry Erdos732
