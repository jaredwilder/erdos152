/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $\alpha$ be an irrational number. Is it true that if, for all large $n$,\[\#\{ 1\leq m\leq n : \{ \alpha m\} \in [u,v)\} = n(v-u)+O(1)\]then $u=\{\alpha k\}$ and $v=\{\alpha \ell\}$ for some integers $k$ and $\ell$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#998 : [Er64b,p.61] analysis | diophantine approximation A problem of Erdős and Szüsz. Hecke [He22] and Ostrowski ( [Os27] and [Os30] ) proved the converse. This is true, and was proved by Kesten [Ke66] . Additional thanks to : Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links This page was last edited 05 October 2025. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #998, https://www.erdosproblems.com/998, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos998

/-- The number of indices `m` with `1 ≤ m ≤ n` whose fractional parts lie in `[u,v)`. -/
noncomputable def intervalCount (α u v : ℝ) (n : ℕ) : ℕ :=
  (Finset.filter
      (fun m : ℕ =>
        1 ≤ m ∧ m ≤ n ∧
          Int.fract (α * (m : ℝ)) ∈ Set.Ico u v)
      (Finset.range (n + 1))).card

/-- Bounded discrepancy for the interval `[u,v)`, formalizing the `O(1)` term in the source. -/
def HasBoundedDiscrepancy (α u v : ℝ) : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |(intervalCount α u v n : ℝ) - (n : ℝ) * (v - u)| ≤ C

/-- The source question, with the standard implicit restriction `0 ≤ u < v ≤ 1`.
The resolution node records that this statement is true, by work of Kesten.
The source clause says that the endpoints are fractional parts of integer multiples
of the same irrational number. -/
def Question : Prop :=
  ∀ α : ℝ, Irrational α →
    ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 →
      HasBoundedDiscrepancy α u v →
        ∃ k l : ℤ,
          u = Int.fract (α * (k : ℝ)) ∧
          v = Int.fract (α * (l : ℝ))

/-- A finite, decidable discrepancy predicate using rational endpoints represented
by numerators modulo a common denominator `q`. The count is tested for every
`n ≤ N`, with additive error at most `C`. -/
def finiteDiscrepancy
    (a q u v N C : ℕ) : Bool :=
  decide
    (0 < q ∧ u ≤ v ∧ v ≤ q ∧
      ∀ n ≤ N,
        q * (Finset.filter
          (fun m : ℕ =>
            1 ≤ m ∧ m ≤ n ∧
              u ≤ (a * m) % q ∧ (a * m) % q < v)
          (Finset.range (n + 1))).card
          ≤ n * (v - u) + C ∧
        n * (v - u) ≤
          q * (Finset.filter
            (fun m : ℕ =>
              1 ≤ m ∧ m ≤ n ∧
                u ≤ (a * m) % q ∧ (a * m) % q < v)
            (Finset.range (n + 1))).card + C)

/-- POSITIVE WITNESS: the full interval `[0,1)` has zero finite discrepancy
for the rational rotation with denominator `1`. -/
theorem finiteDiscrepancy_witness_pos :
    finiteDiscrepancy 1 1 0 1 3 0 = true := by
  decide

/-- NEGATIVE WITNESS: this is a near miss of the positive witness, changing
only the upper endpoint condition from `v ≤ q` to the invalid value `v = 2`. -/
theorem finiteDiscrepancy_witness_neg :
    finiteDiscrepancy 1 1 0 2 3 0 = false := by
  decide

/-- POSITIVE CONTROL: the finite predicate accepts the complete interval
at denominator `1`, so it is not identically false. -/
theorem finiteDiscrepancy_nonvacuous :
    finiteDiscrepancy 1 1 0 1 3 0 = true := by
  decide

/-- NEGATIVE CONTROL: the finite predicate rejects the same instance after
breaking exactly the upper-endpoint constraint. -/
theorem finiteDiscrepancy_rejects_invalid_endpoint :
    finiteDiscrepancy 1 1 0 2 3 0 = false := by
  decide

/-- Kesten's theorem resolves the source question affirmatively.
The proof from the cited literature is not reproduced here. -/
theorem question_resolution : Question := by
  sorry

#print axioms question_resolution

end Erdos998
