/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $d_k(p)$ be the density of those integers whose $k$th smallest prime factor is $p$ (i.e. if $p_1<p_2<\cdots$ are the primes dividing $n$ then $p_k=p$). For fixed $k\geq 1$ is $d_k(p)$ unimodular in $p$? That is, it first increases in $p$ until its maximum then decreases.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#690 : [Er79e] number theory Erdős believes that this is not possible, but could not disprove it. He could show that $p_k$ is about $e^{e^k}$ for almost all $n$, but the maximal value of $d_k(p)$ is assumed for much smaller values of $p$, at\[p=e^{(1+o(1))k}.\]A similar question can be asked if we consider the density of integers whose $k$th smallest divisor is $d$. Erdős could show that this function is not unimodular. Cambie [Ca25] has shown that $d_k(p)$ is unimodular for $1\leq k\leq 3$ and is not unimodular for $4\leq k\leq 20$. Additional thanks to : Stijn Cambie Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (10) Proof claims (0) More information and links This page was last edited 10 May 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #690, https://www.erdosproblems.com/690, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/






import Mathlib
open Classical
open Filter

-- @category research open





open Classical Filter

namespace Erdos690

/-- The predicate that `p` is the `k`th smallest prime factor of `n`.
The convention here is that integers are represented by natural numbers; the
exceptional values `0` and `1` do not affect an eventual natural density. -/
def IsKthSmallestPrimeFactor (k p n : ℕ) : Prop :=
  0 < k ∧ p.Prime ∧ p ∣ n ∧
    (Finset.filter (fun q : ℕ => q.Prime ∧ q ∣ n) (Finset.range p)).card = k - 1

/-- The number of integers below `N` whose `k`th smallest prime factor is `p`. -/
def kthFactorCount (k p N : ℕ) : ℕ :=
  (Finset.filter (fun n : ℕ => IsKthSmallestPrimeFactor k p n) (Finset.range N)).card

/-- `HasNaturalDensity k p d` means that the proportions of integers below `N`
with `k`th smallest prime factor `p` converge to `d`. -/
def HasNaturalDensity (k p : ℕ) (d : ℝ) : Prop :=
  Tendsto
    (fun N : ℕ => (kthFactorCount k p N : ℝ) / (N : ℝ))
    atTop (𝓝 d)

/-- A formal version of unimodality in the prime variable: the density is
nondecreasing up to a prime `m` and nonincreasing after `m`. -/
def UnimodalDensity (k : ℕ) : Prop :=
  ∃ d : ℕ → ℝ, ∃ m : ℕ,
    m.Prime ∧
    (∀ p, p.Prime → HasNaturalDensity k p (d p)) ∧
    (∀ p q, p.Prime → q.Prime → p ≤ q → q ≤ m → d p ≤ d q) ∧
    (∀ p q, p.Prime → q.Prime → m ≤ p → p ≤ q → d q ≤ d p)

/-- The source's question, formalized for every positive fixed `k`. -/
def Question : Prop :=
  ∀ k, 0 < k → UnimodalDensity k

/-- The partial resolution recorded in the source: unimodality for `1 ≤ k ≤ 3`
and failure of unimodality for `4 ≤ k ≤ 20`. -/
def KnownPartial : Prop :=
  (∀ k, 1 ≤ k → k ≤ 3 → UnimodalDensity k) ∧
  (∀ k, 4 ≤ k → k ≤ 20 → ¬ UnimodalDensity k)

/-- A proved sanity check for the definition: `2` is the smallest prime factor
of `6`, while `3` is not its smallest prime factor. -/
theorem kth_factor_control :
    IsKthSmallestPrimeFactor 1 2 6 ∧
      ¬ IsKthSmallestPrimeFactor 1 3 6 := by
  decide

/-- The cited result of Cambie, as recorded by the source. This is an
assumed literature input rather than a proof supplied by this formalization. -/
theorem cambie_partial : KnownPartial := by
  sorry

/-- The recorded partial resolution contradicts the universal affirmative
reading of the question. This derivation is proved from `KnownPartial`. -/
theorem partial_resolution_refutes_question
    (h : KnownPartial) : ¬ Question := by
  intro hq
  have h4 : ¬ UnimodalDensity 4 :=
    h.2 4 (by norm_num) (by norm_num)
  exact h4 (hq 4 (by norm_num))

end Erdos690

#print axioms Erdos690.kth_factor_control
#print axioms Erdos690.partial_resolution_refutes_question
