/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is there a function $f(n)$ and a $k$ such that in any $k$-colouring of the integers there exists a sequence $a_1<\cdots$ such that $a_n<f(n)$ for infinitely many $n$ and the set\[\left\{ \sum_{i\in S}a_i : \textrm{finite }S\right\}\]does not contain all colours?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#948 : [Er77c,p.57] [ErGa91,p.268] number theory | ramsey theory Erdős initially asked whether this is possible with the set being monochromatic, but Galvin showed that this is not always possible, considering the two colouring where, writing $n=2^km$ with $m$ odd, we colour $n$ red if $m\geq F(k)$ and blue if $m<F(k)$ (for some sufficiently quickly growing $F$). In other words, the answer to this question is no when $k=2$. The original question is open even in the case of $\aleph_0$-many colours. This is asked by Erdős and Galvin in [ErGa91] , where they note that they do not even know whether this is possible with $k=3$. In [ErGa91] they do prove that, for all $k\geq 2$, in any $k$-colouring of the integers there is a sequence such that $a_n<2^{2^{O(n)}}$ for all $n$ and\[\left\{ \sum_{i\in I}a_i : \textrm{finite intervals } I\right\}\]is coloured with only two colours. This is asking about a variant of Hindman's theorem (see [532] ). This was answered negatively by GPT Pro (prompted by Price) - in fact, for any function $f$ there is a colouring of $\mathbb{N}$ by $\mathbb{N}$ such that any sequence $a_1<\cdots$ with $a_n<f(n)$ for infinitely many $n$ the set of finite sums from this sequence contains all possible colours (a corresponding result for any finite number of colours follows immediately). Additional thanks to : Stijn Cambie, LouisD, Zach Hunter, and Liam Price Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. Comments (19) Proof claims (0) More information and links This page was last edited 05 July 2026. ( View history ) Erdos Problems #948
-/


import Mathlib
open Classical








open Classical Filter

namespace Erdos948

-- @category research open

/-- The source's question, formalized using integer-valued sequences and
integer colourings.  The question is recorded as open; no theorem asserting
or refuting this proposition is supplied here. -/
def Question : Prop :=
  ∃ f : ℕ → ℤ, ∃ k : ℕ,
    2 ≤ k ∧
      ∀ c : ℤ → Fin k,
        ∃ a : ℕ → ℤ,
          StrictMono a ∧
            (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ a n < f n) ∧
              ∃ col : Fin k,
                ∀ S : Finset ℕ,
                  c (∑ i ∈ S, a i) ≠ col

/-- A finite, decidable bounded pattern on the first `n` indices.
The sequence and its bounds are integer-valued, while `c` colours all
integer finite sums.  This is the finite control used to test the
formalized predicates. -/
def FinitePattern (n k : ℕ) (f a : Fin n → ℤ) (c : ℤ → Fin k) : Prop :=
  2 ≤ k ∧
    StrictMono a ∧
      (∃ i : Fin n, a i < f i) ∧
        ∃ col : Fin k,
          ∀ S : Finset (Fin n),
            c (∑ i ∈ S, a i) ≠ col

/-- POSITIVE WITNESS: a two-term increasing sequence is below its bound at
one index, and a constant colouring omits the other colour from all finite
sums. -/
theorem finitePattern_witness_pos :
    FinitePattern 2 2 ![(10 : ℤ), 10] ![(1 : ℤ), 2]
      (fun _ : ℤ => (0 : Fin 2)) := by
  decide

/-- NEGATIVE WITNESS: this is the preceding instance with exactly one
condition broken: the colouring takes both colours, since the empty sum has
colour zero while the singleton sum `1` has colour one. -/
theorem finitePattern_witness_neg :
    ¬ FinitePattern 2 2 ![(10 : ℤ), 10] ![(1 : ℤ), 2]
      (fun z : ℤ => if z = 0 then (0 : Fin 2) else (1 : Fin 2)) := by
  decide

end Erdos948
