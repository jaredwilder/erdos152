/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Are the squares Ramsey $2$-complete? That is, is it true that, in any 2-colouring of the square numbers, every sufficiently large $n\in \mathbb{N}$ can be written as a monochromatic sum of distinct squares?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#843 : [BuEr85] [Er92b] [Er95] number theory A problem of Burr and Erdős. A similar question can be asked for the set of $k$th powers for any $k\geq 3$. In [Er95] Erdős reported that Burr had proved that the set of $k$th powers is Ramsey $r$ complete for all $r,k\geq 2$, but this result was never published. A stronger version was proved by Conlon, Fox, and Pham [CFP21] , who proved that in fact the set of $k$th powers contains a sparse Ramsey $r$-complete subsequence, again for every $r,k\geq 2$. See also [54] and [55] . Additional thanks to : Sarosh Adenwalla Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #843, https://www.erdosproblems.com/843, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical
open BigOperators

-- @category research solved







open Classical Filter

namespace Erdos843

/-- A colouring of the square numbers is represented by colouring their roots;
since the map `k ↦ k * k` is injective on `ℕ`, this is equivalent to colouring
the set of square numbers. The predicate says that every sufficiently large
natural number is a sum of distinct squares having one common colour. -/
def RamseyTwoComplete : Prop :=
  ∀ c : ℕ → Fin 2,
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ S : Finset ℕ,
        (∑ k ∈ S, k * k) = n ∧
        ∃ col : Fin 2, ∀ k ∈ S, c (k * k) = col

/-- A bounded, decidable test instance: the roots are restricted to `Fin B`,
and the target is the natural number `target`. -/
def FiniteSquareSum (B target : ℕ) (c : Fin B → Fin 2) : Prop :=
  ∃ S : Finset (Fin B),
    (∑ k ∈ S, k.val * k.val) = target ∧
    ∃ col : Fin 2, ∀ k ∈ S, c k = col

/-- POSITIVE WITNESS: the target `5` is the monochromatic sum `1² + 2²`
for the constant zero colouring on the roots below `3`. -/
theorem finiteSquareSum_witness_pos :
    FiniteSquareSum 3 5 (fun _ : Fin 3 => (0 : Fin 2)) := by
  decide

/-- NEGATIVE WITNESS: this is a near miss obtained by changing only the
colour of the root `1`; the unique distinct-square representation
`5 = 1² + 2²` is therefore not monochromatic. -/
theorem finiteSquareSum_witness_neg :
    ¬ FiniteSquareSum 3 5
      (fun k : Fin 3 => if k.val = 1 then (1 : Fin 2) else (0 : Fin 2)) := by
  decide

/-- The frozen resolution reports that Burr proved the square case as part
of the assertion that kth powers are Ramsey r-complete for all `r,k ≥ 2`.
This declaration records that reported literature result; its proof is not
reconstructed here. -/
theorem reported_resolution : RamseyTwoComplete := by
  sorry

#print axioms finiteSquareSum_witness_pos
#print axioms finiteSquareSum_witness_neg

end Erdos843
