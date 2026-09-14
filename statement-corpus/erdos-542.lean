
/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Is it true that if $A\subseteq\{1,\ldots,n\}$ is a set such that $[a,b]>n$ for all $a\neq b$, where $[a,b]$ is the least common multiple, then\[\sum_{a\in A}\frac{1}{a}\leq \frac{31}{30}?\]Is it true that there must be $\gg n$ many $m\leq n$ which do not divide any $a\in A$?

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#542 : [Er73,p.135] [Er80,p.111] [Er98,p.170] number theory The first bound is best possible as $A=\{2,3,5\}$ demonstrates. In [Er80] Erdős dates the second question to 1940. Resolved by Schinzel and Szekeres [ScSz59] who proved the answer to the first question is yes and the answer to the second is no, and in fact there are examples with at most $n/(\log n)^c$ many such $m$, for some constant $c>0$. They further proved that, for any $\epsilon>0$, there is such a sequence for which the sum is $>1-\epsilon$. Chen [Ch96] has proved that if $n>172509$ then\[\sum_{a\in A}\frac{1}{a}< \frac{1}{3}+\frac{1}{4}+\frac{1}{5}+\frac{1}{7}+\frac{1}{11}.\]In [Er73] Erdős further speculates that in fact\[\sum_{a\in A}\frac{1}{a}\leq 1+o(1),\]where the $o(1)$ term $\to 0$ as $n\to \infty$. In [Er98] Erdős mentions that he, Schinzel, and Szekeres conjectured that $2,3,5$ and $3,4,5,7,11$ are the only two sequences for which the sum is $>1$. See also [784] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (3) Proof claims (0) More information and links This page was last edited 08 April 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #542, https://www.erdosproblems.com/542, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

-- @category research solved

import Mathlib
open Classical








open Classical Filter

namespace Erdos542

/-- A finite-set encoding of the source condition: every member lies in
`{1, ..., n}`, and distinct members have least common multiple greater than `n`. -/
def Admissible (n : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ n ∧
    ∀ b ∈ A, a ≠ b → n < Nat.lcm a b

/-- The reciprocal sum appearing in the first question. -/
def ReciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (1 : ℝ) / (a : ℝ)

/-- The first question, formalized as the asserted universal upper bound. -/
def FirstBound : Prop :=
  ∀ n : ℕ, ∀ A : Finset ℕ, Admissible n A →
    ReciprocalSum A ≤ (31 : ℝ) / 30

/-- The members of `{1, ..., n}` which divide no member of `A`. -/
noncomputable def Uncovered (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  {m ∈ Finset.Icc 1 n | ∀ a ∈ A, ¬ m ∣ a}

/-- A precise eventual meaning of “there must be `≫ n` many” uncovered
integers: one positive constant works uniformly for all sufficiently large
`n` and every admissible `A`. -/
def LinearManyUncovered : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → ∀ A : Finset ℕ, Admissible n A →
      c * (n : ℝ) ≤ ((Uncovered n A).card : ℝ)

/-- The second question, under the explicit linear-growth interpretation. -/
def SecondQuestion : Prop :=
  LinearManyUncovered

/-- The source records the first question as settled affirmatively by
Schinzel and Szekeres. The proof of that published result remains to be
formalized here. -/
theorem first_answer : FirstBound := by
  sorry

/-- The source records the second question as settled negatively by
Schinzel and Szekeres. The proof of the counterexamples and their asymptotic
bound remains to be formalized here. -/
theorem second_answer : ¬ SecondQuestion := by
  sorry

/-- The advertised extremal example is admissible at `n = 5`. This is a
proved computational control on the formalized definitions. -/
theorem control_admissible_example :
    Admissible 5 ({2, 3, 5} : Finset ℕ) := by
  decide

/-- The reciprocal sum of the advertised example is exactly `31 / 30`,
showing that the first bound is best possible in the stated normalization. -/
theorem control_extremal_sum :
    ReciprocalSum ({2, 3, 5} : Finset ℕ) = (31 : ℝ) / 30 := by
  norm_num [ReciprocalSum]

#print axioms control_admissible_example
#print axioms control_extremal_sum

end Erdos542
