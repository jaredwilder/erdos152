/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $t_n$ be minimal such that $\{n+1,\ldots,n+t_n\}$ contains a subset whose product with $n$ is a square number (and let $t_n=0$ if $n$ is itself square). Estimate $t_n$.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#841 : [ErSe92] number theory A problem of Erdős, Graham, and Selfridge. For example, $t_6=6$ since $6\cdot 8\cdot 12=24^2$. It is trivial that $t_n\geq P(n)$, where $P(n)$ is the largest prime divisor of $n$. Erdős originally asked whether the set with $t_n\geq n^{1-o(1)}$ has density zero. Selfridge then proved that $t_n=P(n)$ if $P(n)>\sqrt{2n}+1$, and $t_n \ll n^{1/2}$ otherwise. Bui, Pratt, and Zaharescu [BPZ24] proved that the distribution of $t_n$ continues to follow $P(n)$, in that for any fixed $c\in (0,1]$[\lim_{x\to \infty}\frac{\lvert \{ n\leq x : t_n\leq n^c\}\rvert}{x} = \lim_{x\to \infty}\frac{\lvert \{ n\leq x : P(n)\leq n^c\}\rvert}{x}.]They also prove that for at least $x^{1-o(1)}$ many $n\leq x$ we have[\ t_n \leq \exp(O(\sqrt{\log n\log\log n}))\]and for all non-square $n$[\ t_n \gg (\log\log n)^{6/5}(\log\log\log n)^{-1/5}.\]See also [437] . This is problem B30 of Guy's collection [Gu04] . Additional thanks to : Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 14 October 2025. ( View history ) The formalised statement? No ( create one ) OEIS A092487 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research open








open Classical Filter

namespace Erdos841

/-- Whether a natural number is a square, computed using the natural square root. -/
def IsSquareNat (n : ℕ) : Bool :=
  decide (Nat.sqrt n * Nat.sqrt n = n)

/-- POSITIVE WITNESS: zero is a square. -/
theorem IsSquareNat_witness_pos : IsSquareNat 0 = true := by
  decide

/-- NEGATIVE WITNESS: two is the nearest non-square to the positive witness. -/
theorem IsSquareNat_witness_neg : IsSquareNat 2 = false := by
  decide

/-- The source predicate that a finite interval contains a subset whose product with
`n` is a square. The interval is represented by the finite set
`{n + 1, ..., n + t}`, and the empty subset is allowed. -/
def HasSquareProductFinite (n t : ℕ) : Bool :=
  (Finset.Icc (n + 1) (n + t)).powerset.any (fun s =>
    decide
      (Nat.sqrt (n * (∏ x ∈ s, x)) * Nat.sqrt (n * (∏ x ∈ s, x))
        = n * (∏ x ∈ s, x)))

/-- POSITIVE WITNESS: for `n = 6` and `t = 6`, the subset `{8,12}` gives
`6 * 8 * 12 = 24^2`. -/
theorem HasSquareProductFinite_witness_pos :
    HasSquareProductFinite 6 6 = true := by
  decide

/-- NEGATIVE WITNESS: shortening the preceding interval by one changes exactly
the endpoint condition and does not yet contain a suitable subset. -/
theorem HasSquareProductFinite_witness_neg :
    HasSquareProductFinite 6 5 = false := by
  decide

/-- A bounded, decidable version of minimality: either `n` is square and the
answer is zero, or `t` is positive, works in the finite interval, and no
smaller positive endpoint works. -/
def TFinite (n t : ℕ) : Bool :=
  if IsSquareNat n = true then
    decide (t = 0)
  else
    decide (t ≠ 0) &&
      HasSquareProductFinite n t &&
      (Finset.range t).all (fun u =>
        decide (HasSquareProductFinite n u = false))

/-- POSITIVE WITNESS: the example recorded in the source is correctly detected
by the bounded decidable definition. -/
theorem TFinite_witness_pos : TFinite 6 6 = true := by
  decide

/-- NEGATIVE WITNESS: the near miss obtained by decreasing the endpoint from six
to five is not minimal for the required square-product property. -/
theorem TFinite_witness_neg : TFinite 6 5 = false := by
  decide

/-- `HasSquareProduct n t` means that some finite subset of
`{n+1, ..., n+t}` has product with `n` equal to a square. This is the
unbounded mathematical predicate underlying the source's definition. -/
def HasSquareProduct (n t : ℕ) : Prop :=
  ∃ s : Finset ℕ,
    (∀ x ∈ s, n + 1 ≤ x ∧ x ≤ n + t) ∧
      Nat.sqrt (n * (∏ x ∈ s, x)) * Nat.sqrt (n * (∏ x ∈ s, x))
        = n * (∏ x ∈ s, x)

/-- The source's quantity `t_n`, defined as zero for square `n` and otherwise
as the least endpoint satisfying `HasSquareProduct`. The `sInf` is an
extended natural-number infimum; the intended set is nonempty for every
non-square `n`. -/
noncomputable def tValue (n : ℕ) : ℕ :=
  if IsSquareNat n = true then
    0
  else
    sInf {t : ℕ | HasSquareProduct n t}

/-- The concrete example stated in the resolution node. Its proof is left as
an honest gap: the finite computation above verifies the bounded instance,
while connecting that computation to the unbounded `sInf` definition still
requires a separate minimality argument. -/
theorem tValue_six : tValue 6 = 6 := by
  sorry

#print axioms IsSquareNat_witness_pos
#print axioms IsSquareNat_witness_neg
#print axioms HasSquareProductFinite_witness_pos
#print axioms HasSquareProductFinite_witness_neg
#print axioms TFinite_witness_pos
#print axioms TFinite_witness_neg

end Erdos841
