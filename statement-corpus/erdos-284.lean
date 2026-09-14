/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(k)$ be the maximal value of $n_1$ such that there exist $n_1<n_2<\cdots <n_k$ with\[1=\frac{1}{n_1}+\cdots +\frac{1}{n_k}.\]Is it true that\[f(k)=(1+o(1))\frac{k}{e-1}?\]
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#284 : [ErGr80] number theory | unit fractions The upper bound $f(k) \leq (1+o(1))\frac{k}{e-1}$ is trivial since for any $u\geq 1$ we have\[\sum_{u\leq n\leq eu}\frac{1}{n}=1+o(1),\]and hence if $f(k)=u$ then we must have $k\geq (e-1-o(1))u$. Essentially solved by Croot [Cr01] , who showed that for any $N>1$ there exists some $k\geq 1$ and\[N<n_1<\cdots <n_k \leq (e+o(1))N\]with $1=\sum \frac{1}{n_i}$. Additional thanks to : Zachary Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #284, https://www.erdosproblems.com/284, accessed 2026-08-30 From the external database . You can help update this. Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter
open scoped BigOperators Topology

-- @category research solved








open Classical Filter

namespace Erdos284

/-- A strictly increasing list of positive natural-number denominators with first
denominator `n` and reciprocal sum equal to one. -/
def Valid (k n : ℕ) : Prop :=
  ∃ hk : 0 < k, ∃ a : Fin k → ℕ,
    StrictMono a ∧
      (∀ i, 0 < a i) ∧
      a ⟨0, hk⟩ = n ∧
      (∑ i, (1 : ℚ) / (a i : ℚ)) = 1

/-- The literal maximal-value formalization of the function in the source.
The `sSup` is safe only at parameters where the candidate set is nonempty and
bounded above; outside that range Lean's default value is not mathematical. -/
noncomputable def f (k : ℕ) : ℕ :=
  sSup {n : ℕ | Valid k n}

/-- The basic one-term unit-fraction configuration exists. -/
theorem valid_one_one : Valid 1 1 := by
  refine ⟨by decide, (fun _ => 1), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h : i.val < j.val := hij
    omega
  · intro i
    norm_num
  · rfl
  · norm_num [Fin.sum_univ_succ]

/-- The candidate set for `f 1` is nonempty; this is an anti-vacuity control
for the use of `sSup` in the one-term case. -/
theorem candidate_one_nonempty : ({n : ℕ | Valid 1 n} : Set ℕ).Nonempty := by
  exact ⟨1, valid_one_one⟩

/-- The boundedness condition required for interpreting `f k` as a genuine
maximum rather than the junk value of `sSup` on an unbounded set. The proof of
this arithmetic fact is left as an explicit gap. -/
theorem candidate_bddAbove (k : ℕ) :
    BddAbove ({n : ℕ | Valid k n} : Set ℕ) := by
  sorry

/-- The source's asymptotic question, expressed as convergence of the ratio
`f k / k` to `1 / (e - 1)`. -/
def Question : Prop :=
  Tendsto
    (fun k : ℕ => (f k : ℝ) / (k : ℝ))
    atTop
    (𝓝 ((1 : ℝ) / (Real.exp 1 - 1)))

/-- A conditional formalization of the recorded upper-bound statement. The
boundedness and nonemptiness hypotheses explicitly prevent the `sSup` junk
value from making an upper bound vacuous. -/
def RecordedUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ k : ℕ in atTop,
      (BddAbove ({n : ℕ | Valid k n} : Set ℕ) ∧
        ({n : ℕ | Valid k n} : Set ℕ).Nonempty) →
      (f k : ℝ) ≤ (1 + ε) * (k : ℝ) / (Real.exp 1 - 1)

/-- A conditional formalization of the existence direction described in the
resolution: arbitrarily large starting denominators admit a unit-fraction
representation with some number of terms. The precise `o(1)` upper endpoint
is recorded through an explicit tolerance. -/
def RecordedCrootExistence : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ N : ℕ, 1 < N →
      ∃ k : ℕ, ∃ a : Fin k → ℕ,
        0 < k ∧
        StrictMono a ∧
        (∀ i, 0 < a i) ∧
        (N : ℝ) < a ⟨0, by omega⟩ ∧
        (a ⟨k - 1, by omega⟩ : ℝ) ≤ (Real.exp 1 + ε) * N ∧
        (∑ i, (1 : ℚ) / (a i : ℚ)) = 1

#print axioms valid_one_one

end Erdos284
