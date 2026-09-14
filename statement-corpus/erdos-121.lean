/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $F_{k}(N)$ be the size of the largest $A\subseteq \{1,\ldots,N\}$ such that the product of no $k$ many distinct elements of $A$ is a square. Is $F_5(N)=(1-o(1))N$? More generally, is $F_{2k+1}(N)=(1-o(1))N$?

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#121 : [Er94b] [Er97] [Er97e] [Er98] number theory | squares Conjectured by Erdős, Sós, and Sárközy [ESS95] , who proved\[F_2(N)=\left(\frac{6}{\pi^2}+o(1)\right)N,\]\[F_3(N) = (1-o(1))N,\]and also established asymptotics for $F_k(N)$ for all even $k\geq 4$ (in particular, $F_k(N)\asymp N/\log N$ for all even $k\geq 4$). Erdős [Er38] earlier proved that $F_4(N)=o(N)$ - indeed, if $\lvert A\rvert \gg N$ and $A\subseteq \{1,\ldots,N\}$ then there is a non-trivial solution to $ab=cd$ with $a,b,c,d\in A$. Erdős (and independently Hall [Ha96] and Montgomery) also asked about $F(N)$, the size of the largest $A\subseteq\{1,\ldots,N\}$ such that the product of no odd number of $a\in A$ is a square. Ruzsa [Ru77] observed that $1/2<\lim F(N)/N <1$. Granville and Soundararajan [GrSo01] proved an asymptotic\[F(N)=(1-c+o(1))N\]where $c=0.1715\ldots$ is an explicit constant. This problem was answered in the negative by Tao [Ta24] , who proved that for any $k\geq 4$ there is some constant $c_k>0$ such that $F_k(N) \leq (1-c_k+o(1))N$. See also [888] . Additional thanks to : Boris Alexeev Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 17 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #121, https://www.erdosproblems.com/121, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A028391 , A013928 , A372306 , A373319 , A372306 , A373178 , A360659 , A373114 , A143301 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None
-/




import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos121

/-- A natural number is a square when it is the product of two equal natural numbers. -/
def IsSquare (n : ℕ) : Prop :=
  ∃ a : ℕ, n = a * a

/-- 
`Admissible k N A` says that `A` is represented inside `{1, ..., N}`, and that
no `k` distinct elements of `A` have square product.  The explicit cardinality
bound is redundant for the intended finite interval, but makes the boundedness
needed by the supremum definition transparent.
-/
def Admissible (k N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    A.card ≤ N ∧
    ∀ s : Finset ℕ, s ⊆ A → s.card = k →
      ¬ IsSquare (∏ x ∈ s, x)

/-- 
The formal quantity corresponding to the largest size in the source definition.
This uses `sSup`; its boundedness and nonemptiness are supplied below, so the
default value of `sSup` on an unbounded or empty set is not being used.
-/
noncomputable def F (k N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ, Admissible k N A ∧ A.card = m}

/-- The set of candidate cardinalities defining `F k N` is bounded above by `N`. -/
theorem candidate_bddAbove (k N : ℕ) :
    BddAbove {m : ℕ | ∃ A : Finset ℕ, Admissible k N A ∧ A.card = m} := by
  refine ⟨N, ?_⟩
  rintro m ⟨A, hA, rfl⟩
  exact hA.2.1

/-- For positive `k`, the empty set is an admissible candidate. -/
theorem empty_admissible {k N : ℕ} (hk : 0 < k) :
    Admissible k N (∅ : Finset ℕ) := by
  refine ⟨by simp, by simp, ?_⟩
  intro s hs hc hsq
  have he : s = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    exact hs hx
  have hzero : 0 = k := by
    simpa [he] using hc
  omega

/-- For positive `k`, the candidate set defining `F k N` is nonempty. -/
theorem candidate_nonempty {k N : ℕ} (hk : 0 < k) :
    Set.Nonempty
      {m : ℕ | ∃ A : Finset ℕ, Admissible k N A ∧ A.card = m} := by
  refine ⟨0, ?_⟩
  exact ⟨∅, empty_admissible hk, by simp⟩

/-- A proved sanity control: one is a square, so the square predicate is nontrivial. -/
theorem square_one : IsSquare 1 := by
  exact ⟨1, by norm_num [IsSquare]⟩

/-- 
The asymptotic statement represented by `(1-o(1))N`: for every positive
epsilon, eventually `F k N` lies between `(1-epsilon)N` and `(1+epsilon)N`.
-/
def LinearDensityOne (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 - ε) * (N : ℝ) ≤ (F k N : ℝ) ∧
        (F k N : ℝ) ≤ (1 + ε) * (N : ℝ)

/-- The question for `k = 5`, namely whether `F₅(N)=(1-o(1))N`. -/
def QuestionFive : Prop :=
  LinearDensityOne 5

/-- The general question for odd indices, namely whether `F_{2k+1}(N)=(1-o(1))N`. -/
def QuestionOdd : Prop :=
  ∀ k : ℕ, LinearDensityOne (2 * k + 1)

/-- 
The source's resolution says that the proposed asymptotic fails for every
`k ≥ 4`.  This declaration records that settled literature result as an
explicit proof gap rather than as an axiom; its analytic number-theoretic
proof is not reproduced here.
-/
theorem tao_negative {k : ℕ} (hk : 4 ≤ k) :
    ¬ LinearDensityOne k := by
  sorry

/-- In particular, the answer to the `k = 5` question is negative. -/
theorem answer_five : ¬ QuestionFive := by
  intro h
  exact tao_negative (k := 5) (by omega) h

end Erdos121

#print axioms Erdos121.square_one
