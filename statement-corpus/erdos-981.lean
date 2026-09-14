/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $\epsilon>0$ and $f_\epsilon(p)$ be the smallest integer $m$ such that $\sum_{n\leq N} \left(\frac{n}{p}\right)<\epsilon N$ for all $N\geq m$. Prove that\[\sum_{p<x}f_\epsilon(p)\sim c_\epsilon \frac{x}{\log x}\]for some $c_\epsilon>0$.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#981 : [Er65b,p.232] number theory This was proved by Elliott [El69] . An earlier version of this problem on this site misstated the problem, defining $f_\epsilon(p)$ instead as the smallest integer $m$ such that $\sum_{n\leq m}\binom{n}{p}<\epsilon m$ (thus a 'first-time' problem rather than the 'eventual-time' problem given above). An asymptotic for this alternate definition of $f_\epsilon$ was proved by Tang and Zhang [TaZh25] . Additional thanks to : Quanyu Tang Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (4) Proof claims (0) More information and links This page was last edited 27 December 2025. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #981, https://www.erdosproblems.com/981, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable None Working on formalising None Previous Next
-/


-- @category research solved








import Mathlib
open Classical Filter

namespace Erdos981

/-- A direct finite definition of the quadratic character used here.  For prime
moduli this is the Legendre symbol: it is zero on multiples of the modulus,
one on nonzero quadratic residues, and minus one otherwise. -/
def quadraticCharacter (n p : ℕ) : ℤ :=
  if p ≤ 1 then 0
  else if p ∣ n then 0
  else if ∃ a ∈ Finset.range p, a ^ 2 % p = n % p then 1
  else -1

/-- The bounded, decidable version of the eventual inequality in the source.
The parameter `N` restricts the universal quantifier to `k < N`. -/
def finiteCharacterBound (ε : ℚ) (p m N : ℕ) : Bool :=
  decide
    (∀ k ∈ Finset.range N, m ≤ k →
      ((∑ n ∈ Finset.range (k + 1), quadraticCharacter n p : ℤ) : ℚ) < ε * k)

/-- POSITIVE WITNESS: for the modulus `3`, epsilon `1/2`, and threshold `2`,
the bounded eventual inequality holds through `k < 8`. -/
theorem finiteCharacterBound_witness_pos :
    finiteCharacterBound ((1 : ℚ) / 2) 3 2 8 = true := by
  decide

/-- NEGATIVE WITNESS: this is the near miss obtained from the positive
witness by lowering the threshold from `2` to `1`; the condition fails at
the first newly included value `k = 1`. -/
theorem finiteCharacterBound_witness_neg :
    finiteCharacterBound ((1 : ℚ) / 2) 3 1 8 = false := by
  decide

/-- The eventual-time quantity from the source.  It is defined as the natural
infimum of the set of thresholds satisfying the inequality for every
`N ≥ m`; the source's theorem concerns this quantity only at prime moduli.
The use of `sInf` is safe in the stated theorem because the source asserts
that this smallest threshold exists; the finite predicate above supplies a
computable bounded control rather than relying on the default value of an
unbounded infimum. -/
noncomputable def f (ε : ℚ) (p : ℕ) : ℕ :=
  sInf
    {m : ℕ |
      ∀ N : ℕ, m ≤ N →
        ((∑ n ∈ Finset.range (N + 1), quadraticCharacter n p : ℤ) : ℚ) < ε * N}

/-- Formalization of the resolved claim.  The source sentence
`sum_{p<x} f_epsilon(p) sim c_epsilon x/log x` is read as convergence of
the quotient of the left-hand side by `x/log x` to a positive real
constant, with the sum taken over primes `p < x`.  The result is recorded
as proved in the source by Elliott; the analytic number-theoretic proof is
not reproduced in this entry. -/
theorem erdos981 :
    ∀ ε : ℚ, 0 < ε →
      ∃ c : ℝ, 0 < c ∧
        Tendsto
          (fun x : ℕ =>
            ((∑ p ∈ Finset.filter Nat.Prime (Finset.range x), f ε p : ℕ) : ℝ) /
              ((x : ℝ) / Real.log x))
          Filter.atTop (𝓝 c) := by
  sorry

#print axioms erdos981

end Erdos981
