/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
For integers $1\leq a<b$ let $D(a,b)$ be the minimal value of $n_k$ such that there exist integers $1\leq n_1<\cdots <n_k$ with\[\frac{a}{b}=\frac{1}{n_1}+\cdots+\frac{1}{n_k}.\]Estimate $D(b)=\max_{1\leq a<b}D(a,b)$. Is it true that\[D(b) \ll b(\log b)^{1+o(1)}?\]
-/

/- 
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#305 : [ErGr80,p.38] number theory | unit fractions Bleicher and Erdős [BlEr76] have shown that\[D(b)\ll b(\log b)^2.\]If $b=p$ is a prime then\[D(p) \gg p\log p.\]This was solved by Yokota [Yo88] , who proved that\[D(b)\ll b(\log b)(\log\log b)^4(\log\log\log b)^2.\]This was improved by Liu and Sawhney [LiSa24] to\[D(b)\ll b(\log b)(\log\log b)^3(\log\log\log b)^{O(1)}.\] Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 18 November 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #305, https://www.erdosproblems.com/305, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos305

/-- A finite strictly increasing Egyptian-fraction representation of `a / b`
whose last denominator is `m`. -/
def ValidRep (a b m : ℕ) : Prop :=
  ∃ k : ℕ, ∃ n : Fin (k + 1) → ℕ,
    0 < n 0 ∧
      (∀ i j, i < j → n i < n j) ∧
      (∑ i, (1 : ℚ) / (n i : ℚ) = (a : ℚ) / (b : ℚ)) ∧
      n ⟨k, by omega⟩ = m

/-- The denominator set used to define `D(a,b)`.  The `sInf` convention is
safe on the intended domain because a representation-existence result supplies
nonemptiness there; outside that domain the definition deliberately retains
Lean's default value rather than silently asserting a number-theoretic claim. -/
def RepDenoms (a b : ℕ) : Set ℕ :=
  {m | ValidRep a b m}

/-- The minimal final denominator in an Egyptian-fraction representation of
`a / b`. -/
noncomputable def D (a b : ℕ) : ℕ :=
  sInf (RepDenoms a b)

/-- The maximum of `D(a,b)` over the integers `a` with `1 ≤ a < b`. -/
def Dmax (b : ℕ) : ℕ :=
  (Finset.Icc 1 (b - 1)).sup (fun a => D a b)

/-- The standard existence theorem for finite Egyptian-fraction expansions,
recorded here as the mathematical input needed to ensure that the `sInf`
defining `D` is not the empty-set junk value on the source's domain. -/
theorem representation_exists {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    (RepDenoms a b).Nonempty := by
  sorry

/-- On the intended range `1 ≤ a < b`, the set defining `D(a,b)` is
nonempty, so its `sInf` is mathematically controlled rather than the empty-set
default. -/
theorem repDenoms_nonempty {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    (RepDenoms a b).Nonempty :=
  representation_exists ha hab

/-- A concrete sanity check: `1/2` has the one-term representation with
denominator `2`.  This is a proved control exercising the representation
predicate itself. -/
theorem validRep_one_two : ValidRep 1 2 2 := by
  refine ⟨0, (fun _ => 2), ?_, ?_, ?_, rfl⟩
  · norm_num
  · intro i j hij
    have h : i = j := by
      apply Fin.eq_of_val_eq
      omega
    exact (False.elim (by simpa [h] using hij))
  · norm_num [Fin.sum_univ_succ]

/-- A precise formal reading of the question's `(\log b)^{1+o(1)}` upper
bound: every positive exponent slack is eventually absorbed into a constant. -/
def Question : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, ∀ b : ℕ, B ≤ b →
      (Dmax b : ℝ) ≤ C * (b : ℝ) *
        Real.rpow (Real.log (b : ℝ)) (1 + ε)

/-- A formalized version of the Liu--Sawhney resolution.  The source writes
the final exponent as `O(1)`; here this is represented by the existence of a
fixed real exponent `q`. -/
def LiuSawhneyBound : Prop :=
  ∃ C q : ℝ, 0 < C ∧ ∃ B : ℕ, ∀ b : ℕ, B ≤ b →
    (Dmax b : ℝ) ≤ C * (b : ℝ) *
      Real.log (b : ℝ) *
      Real.rpow (Real.log (Real.log (b : ℝ))) 3 *
      Real.rpow (Real.log (Real.log (Real.log (b : ℝ)))) q

/-- The settled literature result recorded in the source, treated as an
external mathematical input rather than proved in this file. -/
theorem liu_sawhney_bound : LiuSawhneyBound := by
  sorry

/-- The recorded improved bound answers the original `1+o(1)` question. -/
theorem question_follows_from_liu_sawhney :
    LiuSawhneyBound → Question := by
  sorry

#print axioms validRep_one_two

end Erdos305
