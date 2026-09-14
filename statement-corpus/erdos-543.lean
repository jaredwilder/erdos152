/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Define $f(N)$ be the minimal $k$ such that the following holds: if $G$ is an abelian group of size $N$ and $A\subseteq G$ is a random set of size $k$ then, with probability $\geq 1/2$, all elements of $G$ can be written as $\sum_{x\in S}x$ for some $S\subseteq A$. Is\[f(N) \leq \log_2 N+o(\log\log N)?\]

NODE n001-resolution (resolution), VERBATIM:
#543 : [Er73,p.127] [ErHa78b] number theory | group theory Erdős and Rényi [ErRe65] proved that\[f(N) \leq \log_2N+O(\log\log N).\]Erdős believed improving this to $o(\log\log N)$ is impossible. Erdős and Hall [ErHa78b] proved that it is not true that\[f(N) \leq \log_2N+o(\log\log\log N).\]ChatGPT and Tang have disproved this , confirming Erdős' belief, showing that if $f(N)\leq \log_2 N+o(\log\log N)$ then, for all large enough primes $p$, a random subset of $\mathbb{F}_p$ of size $\leq f(p)$ fails to generate $\mathbb{F}_p$ in this way. See also [1179] . Additional thanks to : KoishiChan Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (30) Proof claims (0) More information and links This page was last edited 27 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #543, https://www.erdosproblems.com/543, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter








open Classical Filter

namespace Erdos543

-- @category research solved

/-- `subsetSumComplete A` says that every element of the ambient finite additive
commutative group is a sum of a subset of `A`. -/
def subsetSumComplete {G : Type} [AddCommGroup G] [Fintype G]
    (A : Finset G) : Prop :=
  ∀ g : G, ∃ S : Finset G, S ⊆ A ∧ (∑ x ∈ S, x) = g

/-- The finite sample space of random subsets of `G` having cardinality `k`. -/
def samples {G : Type} [AddCommGroup G] [Fintype G]
    (k : ℕ) : Finset (Finset G) :=
  (Finset.univ : Finset (Finset G)).filter (fun A => A.card = k)

/-- The number of sampled subsets for which all group elements are subset sums. -/
def successfulSamples {G : Type} [AddCommGroup G] [Fintype G]
    (k : ℕ) : ℕ :=
  ((samples k).filter subsetSumComplete).card

/-- `good G k` formalizes probability at least one half by counting the uniform
finite sample space of `k`-element subsets. -/
def good {G : Type} [AddCommGroup G] [Fintype G]
    (k : ℕ) : Prop :=
  2 * successfulSamples k ≥ (samples k).card

/-- The assertion that a random `k`-element subset works with probability at
least one half for every abelian group of order `N`. -/
def universallyGood (N k : ℕ) : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G],
    Fintype.card G = N → good G k

/-- The minimal `k` in the source problem, using `Nat.find` when a suitable
value exists and returning `0` only in the otherwise-unused fallback case. -/
noncomputable def f (N : ℕ) : ℕ :=
  if h : ∃ k : ℕ, universallyGood N k then Nat.find h else 0

/-- A logarithm to base two, matching the notation in the source. -/
def logTwo (N : ℕ) : ℝ :=
  Real.log (N : ℝ) / Real.log 2

/-- The logarithmic scale occurring in the little-oh term of the source. -/
def logLog (N : ℕ) : ℝ :=
  Real.log (Real.log (N : ℝ))

/-- The formalized question: the error is represented by a sequence tending to
zero, and the displayed inequality is required eventually. -/
def Question : Prop :=
  ∃ r : ℕ → ℝ,
    Tendsto r atTop (𝓝 0) ∧
      ∀ᶠ N : ℕ in atTop,
        (f N : ℝ) ≤ logTwo N + r N * logLog N

/-- The source records the question as settled negatively. A complete proof of
this literature result remains to be formalized; the statement is not used as
an axiom. -/
theorem resolution_not_question : ¬ Question := by
  sorry

/-- Every element of a finite additive commutative group is a subset sum of the
whole group. This is a proved control exercising the central subset-sum
definition. -/
theorem univ_subsetSumComplete (G : Type) [AddCommGroup G] [Fintype G] :
    subsetSumComplete (Finset.univ : Finset G) := by
  intro g
  refine ⟨{g}, ?_, ?_⟩
  · simp
  · simp

#print axioms univ_subsetSumComplete

end Erdos543
