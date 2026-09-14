/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
If $\mathcal{F}$ is a family of subsets of $\{1,\ldots,n\}$ then we write $G_{\mathcal{F}}$ for the graph on $\mathcal{F}$ where $A\sim B$ if $A$ and $B$ are comparable - that is, $A\subseteq B$ or vice versa. Is it true that, if $\epsilon>0$ and $n$ is sufficiently large, whenever $m\leq (2-\epsilon)2^{n/2}$ the graph $G_\mathcal{F}$ has $<2^{n}$ many edges? Is it true that if $G_{\mathcal{F}}$ has $\geq cm^2$ edges then $m\ll_c 2^{n/2}$? Is it true that, for any $\epsilon>0$, there exists some $\delta>0$ such that if there are $>m^{2-\delta}$ edges then $m<(2+\epsilon)^{n/2}$?
-/

/-
RESOLUTION (frozen), node `n001-resolution`, VERBATIM:
#777 : [Gu83] graph theory | combinatorics A problem of Daykin and Erdős. Daykin and Frankl proved that if there are $(1+o(1))\binom{m}{2}$ edges then $m^{1/n}\to 1$ as $n\to \infty$. For the first question we need to take $\epsilon>0$ since since if $n$ is even and $m=2^{n/2+1}$ one could take $\mathcal{F}$ to be all subsets of $\{1,\ldots,n/2\}$ together with $\{1,\ldots,n/2\}$ union all subsets of $\{n/2+1,\ldots,n\}$, which produces $2^{n}$ edges. The third question was answered in the affirmative by Alon and Frankl [AlFr85] , who proved that, for every $k\geq 1$, if $m=2^{(\frac{1}{k+1}+\delta)n}$ for some $\delta>0$ then the number of edges is\[< \left(1-\frac{1}{k}\right)\binom{m}{2}+O(m^{2-\Omega_k(\delta^{k+1})}).\]They also answer the second question in the negative, noting that if $\mathcal{F}$ is the family of sets which either intersect $\{n/2+1,\ldots,n\}$ in at most $1$ element or intersect $\{1,\ldots,n/2\}$ in at least $n/2-1$ elements then $m \gg n2^{n/2}$ and there are at least $2^{-5}\binom{m}{2}$ edges. Finally, an affirmative answer to the first question follows from Theorem 1.4 and Corollary 1.5 of Alon, Das, Glebov, and Sudakov [ADGS15] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #777, https://www.erdosproblems.com/777, accessed 2026-08-30 From the external database . You can help update this. Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos777

/-- Two subsets are comparable when one is contained in the other. -/
def Comparable {n : ℕ} (A B : Finset (Fin n)) : Prop :=
  A ⊆ B ∨ B ⊆ A

/-- The comparability relation is symmetric. -/
theorem comparable_comm {n : ℕ} {A B : Finset (Fin n)} :
    Comparable A B ↔ Comparable B A := by
  constructor <;> intro h
  · rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- The empty subset is comparable with every subset. -/
theorem comparable_empty_left {n : ℕ} (A : Finset (Fin n)) :
    Comparable ∅ A := by
  exact Or.inl Finset.empty_subset

/-- The number of edges of the graph on `F` whose edges join distinct comparable
members. The double sum counts each undirected edge twice, so it is divided by
two. -/
noncomputable def edgeCount (n : ℕ) (F : Finset (Finset (Fin n))) : ℕ :=
  (F.sum (fun A =>
    (F.erase A).sum (fun B => if Comparable A B then 1 else 0))) / 2

/-- A proved control showing that the edge-count definition has the expected
value on a one-vertex graph. -/
theorem edgeCount_singleton (n : ℕ) :
    edgeCount n ({∅} : Finset (Finset (Fin n))) = 0 := by
  simp [edgeCount]

/-- The first question, formalized with the literal meaning of
"sufficiently large" and with `m` equal to the cardinality of the family. -/
def FirstQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n ≥ N, ∀ F : Finset (Finset (Fin n)),
      (F.card : ℝ) ≤ (2 - ε) * (2 : ℝ) ^ (n / 2) →
        edgeCount n F < 2 ^ n

/-- The second question, formalized by interpreting `m ≪_c 2^(n/2)` as an
eventual bound by `C * 2^(n/2)` for a constant depending on `c`. -/
def SecondQuestion : Prop :=
  ∀ c : ℝ, 0 < c →
    ∃ C : ℝ, 0 < C ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ F : Finset (Finset (Fin n)),
        c * (F.card : ℝ) ^ 2 ≤ (edgeCount n F : ℝ) →
          (F.card : ℝ) ≤ C * (2 : ℝ) ^ (n / 2)

/-- The third question, formalized using `Real.rpow` for the real exponent
`2 - δ`. -/
def ThirdQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ F : Finset (Finset (Fin n)),
        Real.rpow (F.card : ℝ) (2 - δ) < (edgeCount n F : ℝ) →
          (F.card : ℝ) < Real.rpow (2 + ε) (n / 2)

/-- The affirmative answer to the first question recorded in the source.
The proof from Alon, Das, Glebov, and Sudakov is not formalized here; this is
an explicit honest gap for that literature result. -/
theorem first_question_resolved : FirstQuestion := by
  sorry

/-- The negative answer to the second question recorded in the source. The
counterexample construction and its asymptotic estimates remain unformalized. -/
theorem second_question_resolved : ¬ SecondQuestion := by
  sorry

/-- The affirmative answer to the third question recorded in the source. The
Alon--Frankl estimate is not formalized here; this declaration records the
remaining literature-dependent gap explicitly. -/
theorem third_question_resolved : ThirdQuestion := by
  sorry

#print axioms edgeCount_singleton

end Erdos777
