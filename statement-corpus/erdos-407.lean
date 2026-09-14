/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $w(n)$ count the number of solutions to\[n=2^a+3^b+2^c3^d\]with $a,b,c,d\geq 0$ integers. Is it true that $w(n)$ is bounded by some absolute constant?

NODE n001-resolution (resolution), VERBATIM:
#407 : [ErGr80,p.80] number theory A conjecture originally due to Newman. This is true, and was proved by Evertse, Györy, Stewart, and Tijdeman [EGST88] . Quantitative bounds were provided by Tijdeman and Wang [TiWa88] , who proved that (if $w(n)$ only counts distinct solutions, where we call two solutions distinct if the sets $\{2^a,3^b,2^{c}3^d\}$ are distinct) then $w(n) \leq 4$ for all large $n$. This was made effective by Bajpai and Bennett [BaBe24] , who proved that $w(n)\leq 4$ if $n\geq 131082$ and $w(n)\leq 9$ for all $n$. (The largest $n$ for which $w(n)=9$ is $299$.) There are infinitely many $n$ with $w(n)=4$, given by the identities \begin{align*} 2^{a-1}+3^b+2^{a-1}3^0 &= 2^{a-2}+3^b+2^{a-2}3^1\\ &=2^a+3^{b-1}+2\cdot 3^{b-1}\\ &=2^a+3^{b-2}+2^33^{b-2}. \end{align*} Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (5) Proof claims (0) More information and links This page was last edited 18 November 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #407, https://www.erdosproblems.com/407, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS possible, A387688 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos407

/-- A quadruple of nonnegative exponents bounded by `n`, represented using four
copies of `Fin (n + 1)`. -/
abbrev BoundedExponents (n : ℕ) :=
  (Fin (n + 1) × Fin (n + 1)) × (Fin (n + 1) × Fin (n + 1))

/-- The set `{2^a, 3^b, 2^c 3^d}` associated with a bounded exponent
quadruple.  Finset equality is exactly the distinctness convention stated in
the resolution. -/
def valueSet {n : ℕ} (q : BoundedExponents n) : Finset ℕ :=
  {2 ^ q.1.1.val, 3 ^ q.1.2.val, 2 ^ q.2.1.val * 3 ^ q.2.2.val}

/-- The finite collection of distinct solution-sets for `n`.  Every genuine
solution has exponents at most `n` when `n > 0`, since each summand is at most
the sum; the `n = 0` case has no solutions. -/
def solutionSets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.univ.filter (fun q : BoundedExponents n =>
    2 ^ q.1.1.val + 3 ^ q.1.2.val +
        2 ^ q.2.1.val * 3 ^ q.2.2.val = n)).image valueSet

/-- The formalized counting function `w`, counting distinct solution-sets rather
than syntactically distinct exponent quadruples, as specified in the known
resolution. -/
def w (n : ℕ) : ℕ :=
  (solutionSets n).card

/-- A proved small-value control: the defining predicate is nonvacuous, since
there is exactly one distinct solution-set for `n = 3`. -/
theorem w_three : w 3 = 1 := by
  decide

/-- A proved degenerate-value control: there are no solutions for `n = 0`. -/
theorem w_zero : w 0 = 0 := by
  decide

/-- The effective global estimate reported in the resolution, namely
`w(n) ≤ 9` for every natural number `n`.  This declaration records the
literature result as an explicit honest proof gap. -/
theorem global_bound : ∀ n : ℕ, w n ≤ 9 := by
  sorry

/-- The effective eventual estimate reported in the resolution: if
`n ≥ 131082`, then `w(n) ≤ 4`.  This declaration records the literature
result as an explicit honest proof gap. -/
theorem eventual_bound : ∀ n : ℕ, 131082 ≤ n → w n ≤ 4 := by
  sorry

/-- The source question, formalized as the existence of an absolute natural
upper bound for the distinct-solution counting function. -/
def AbsoluteBound : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, w n ≤ C

/-- The source question is answered affirmatively, derived from the assumed
global estimate above.  The proof body is checked by Lean; its only
non-kernel input is `global_bound`. -/
theorem absolute_bound : AbsoluteBound := by
  refine ⟨9, ?_⟩
  intro n
  exact global_bound n

#print axioms w_three
#print axioms w_zero
#print axioms absolute_bound

end Erdos407
