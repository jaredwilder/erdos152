/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
If $P(m)$ is the greatest prime divisor of $m$, then is it true that\[\frac{P(2^n-1)}{n}\to \infty\]as $n\to \infty$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#977 : [Er65b] number theory Schinzel [Sc62] proved that $P(2^n-1)>2n$ for $n>12$. In [Er65b] Erdős also asks about $P(n!+1)$. Stewart [St74b] proved that this conjecture is true if we restrict $n$ to those integers with $<\frac{1}{\log 2}\log\log n$ many prime factors. This was proved in the affirmative by Stewart [St13] , who proved that\[P(2^n-1)\gg n^{1+\frac{1}{104\log\log n}}\]for all large $n$. The case of $P(n!+1)$ appears to be open still. Murty and Wong [MuWo02] proved that\[P(n!+1)>(1+o(1))n\log n\]assuming the abc conjecture. The best-known unconditional result, due to Lai [La21] , is that\[\limsup \frac{P(n!+1)}{n} \geq 1+9\log 2\approx 7.238.\] Additional thanks to : Alfaiz and Mehtaab Sawhney Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (2) Proof claims (0) More information and links This page was last edited 01 February 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #977, https://www.erdosproblems.com/977, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A005420 , A002583 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


-- @category research solved

import Mathlib
open Classical
open Filter








open Classical Filter

namespace Erdos977

/-- A computable auxiliary search for the largest prime divisor among the numbers below `k`. -/
def greatestPrimeDivisorAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, m =>
      if Nat.Prime k ∧ k ∣ m then
        max k (greatestPrimeDivisorAux k m)
      else
        greatestPrimeDivisorAux k m

/-- The greatest prime divisor function, with value `0` when there is no prime divisor. -/
def greatestPrimeDivisor (m : ℕ) : ℕ :=
  greatestPrimeDivisorAux (m + 1) m

/-- The mathematical predicate saying that `p` is the greatest prime divisor of `m`. -/
def IsGreatestPrimeDivisor (m p : ℕ) : Prop :=
  Nat.Prime p ∧ p ∣ m ∧
    ∀ q : ℕ, Nat.Prime q → q ∣ m → q ≤ p

/-- A bounded, decidable version of being the greatest prime divisor. -/
def IsGreatestPrimeDivisorFinite (m p b : ℕ) : Bool :=
  decide
    (Nat.Prime p ∧ p ∣ m ∧
      ∀ q ∈ Finset.range (b + 1), Nat.Prime q → q ∣ m → q ≤ p)

/-- POSITIVE WITNESS: `7` is the greatest prime divisor of `7` when testing primes up to `7`. -/
theorem isGreatestPrimeDivisorFinite_witness_pos :
    IsGreatestPrimeDivisorFinite 7 7 7 = true := by
  decide

/-- NEGATIVE WITNESS: the near-miss `p = 3` fails only the divisibility condition for `m = 7`. -/
theorem isGreatestPrimeDivisorFinite_witness_neg :
    IsGreatestPrimeDivisorFinite 7 3 7 = false := by
  decide

/-- Concrete control: the computable greatest-prime-divisor function has value `7` at `7`. -/
theorem greatestPrimeDivisor_control_pos :
    greatestPrimeDivisor 7 = 7 := by
  decide

/-- Concrete control: `5` is a near-miss for the value of the function at `7`. -/
theorem greatestPrimeDivisor_control_neg :
    greatestPrimeDivisor 7 ≠ 5 := by
  decide

/-- The computed function agrees with the greatest-prime-divisor predicate for integers at least `2`.
The proof is left as an explicit gap for the elementary verification of the recursive search. -/
theorem greatestPrimeDivisor_spec {m : ℕ} (hm : 2 ≤ m) :
    IsGreatestPrimeDivisor m (greatestPrimeDivisor m) := by
  sorry

/-- The question from the source: the ratio of the greatest prime divisor of `2^n - 1`
to `n` tends to infinity along the natural numbers. -/
def Question : Prop :=
  Tendsto
    (fun n : ℕ =>
      (greatestPrimeDivisor (2 ^ n - 1) : ℝ) / (n : ℝ))
    atTop atTop

/-- A bounded decidable approximation to the question, asking for the ratio numerator
to be at least `K` for every index in the finite range through `N`. -/
def QuestionFinite (N K : ℕ) : Bool :=
  decide
    (∀ n ∈ Finset.range (N + 1),
      K ≤ greatestPrimeDivisor (2 ^ n - 1))

/-- POSITIVE WITNESS: the bounded approximation is true at the vacuous threshold `K = 0`
on the singleton index range through `N = 0`. -/
theorem questionFinite_witness_pos :
    QuestionFinite 0 0 = true := by
  decide

/-- NEGATIVE WITNESS: the near-miss obtained by increasing the threshold to `K = 1`
fails already at the index `n = 0`. -/
theorem questionFinite_witness_neg :
    QuestionFinite 0 1 = false := by
  decide

/-- Stewart's affirmative resolution of the source question, formalized as a literature-derived
claim. The remaining gap is the analytic number-theoretic proof that the displayed sequence
tends to infinity. -/
theorem question_answered : Question := by
  sorry Erdos977

#print axioms Erdos977.isGreatestPrimeDivisorFinite_witness_pos
#print axioms Erdos977.isGreatestPrimeDivisorFinite_witness_neg
#print axioms Erdos977.greatestPrimeDivisor_control_pos
#print axioms Erdos977.greatestPrimeDivisor_control_neg
