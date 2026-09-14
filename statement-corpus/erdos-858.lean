/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $A\subseteq \{1,\ldots,N\}$ be such that there is no solution to $at=b$ with $a,b\in A$ and the smallest prime factor of $t$ is $>a$. Estimate the maximum of\[\frac{1}{\log N}\sum_{n\in A}\frac{1}{n}.\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#858 : [Er70,p.128] number theory | primitive sets Alexander [Al66] and Erdős, Sárközi, and Szemerédi [ESS68] proved that if $A$ is an infinite set with this property then\[\sum_{n\in A\cap [1,N]}\frac{1}{n}=o(\log N)\](at a rate which depends on $A$), and furthermore for any fixed large $N$ the supremum in this question is bounded away from $0$. This condition on $A$ is a weaker form of the usual primitive condition. If $A$ is primitive then Behrend [Be35] proved\[\frac{1}{\log N}\sum_{n\in A}\frac{1}{n}\ll \frac{1}{\sqrt{\log\log N}}.\]An example of such a set $A$ is the set of all integers in $[N^{1/2},N]$ divisible by some prime $>N^{1/2}$. This has been solved by Chojecki and GPT-5.4 Pro (see the comments), who show that for large $N\[\max_A \sum_{n\in A}\frac{1}{n}=(c+o(1))\log N\]where the maximum is over all $A\subseteq \{1,\ldots,N\}$ with the stated property and $c\approx 0.618\cdots$ is an explicit constant. See also [143] . Additional thanks to : Terence Tao and Desmond Weisenberg Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. Comments (13) Proof claims (0) More information and links This page was last edited 24 April 2026. ( View history ) (https://www.erdosproblems.com/858)
-/






import Mathlib
open Classical
open Filter

-- @category research solved






open Classical Filter

namespace Erdos858

/-- The exact property from the source: `Admissible A N` means that `A` is
contained in `1 ≤ n ≤ N`, and there are no `a,b ∈ A` and `t ≥ 2` with
`at = b` and smallest prime factor of `t` greater than `a`. -/
def Admissible (N : ℕ) (A : Set ℕ) : Prop :=
  A ⊆ Set.Icc 1 N ∧
    ∀ a ∈ A, ∀ b ∈ A, ∀ t : ℕ,
      2 ≤ t → a * t = b → Nat.minFac t ≤ a

/-- The bounded decidable version of `Admissible`, restricting `t` to
`2 ≤ t ≤ N`; this is equivalent for solutions with `a,b ∈ [1,N]`. -/
def AdmissibleFinite (N : ℕ) (A : Finset ℕ) : Bool :=
  decide (
    (∀ n ∈ A, n ∈ Finset.Icc 1 N) ∧
      ∀ a ∈ A, ∀ b ∈ A, ∀ t ∈ Finset.Icc 2 N,
        a * t = b → Nat.minFac t ≤ a)

/-- POSITIVE WITNESS: the singleton set satisfies the source condition at `N = 1`. -/
theorem admissible_witness_pos :
    AdmissibleFinite 1 ({1} : Finset ℕ) = true := by
  decide

/-- NEGATIVE WITNESS: adjoining `2` to the positive witness creates exactly
the forbidden relation `1 * 2 = 2`, whose smallest prime factor is greater
than `1`. -/
theorem admissible_witness_neg :
    AdmissibleFinite 2 ({1, 2} : Finset ℕ) = false := by
  decide

/-- POSITIVE WITNESS: the singleton set satisfies the unbounded formulation
of the source condition. -/
theorem admissible_set_witness_pos :
    Admissible 1 ({1} : Set ℕ) := by
  constructor
  · intro n hn
    simp at hn
    simpa [hn]
  · intro a ha b hb t ht hab
    have ha' : a = 1 := by simpa using ha
    have hb' : b = 1 := by simpa using hb
    subst a
    subst b
    omega

/-- NEGATIVE WITNESS: the near-miss set `{1,2}` violates the unbounded
formulation by the single relation `1 * 2 = 2`. -/
theorem admissible_set_witness_neg :
    ¬ Admissible 2 ({1, 2} : Set ℕ) := by
  intro h
  have q := h.2 1 (by simp) 2 (by simp) 2 (by norm_num) (by norm_num)
  norm_num at q

/-- The reciprocal weight appearing in the source's extremal expression. -/
def reciprocalWeight (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, (1 : ℝ) / (n : ℝ)

/-- The finite collection of admissible sets contained in `[1,N]`. -/
def admissibleCandidates (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.powerset (Finset.Icc 1 N)).filter (fun A => AdmissibleFinite N A)

/-- The finite set of reciprocal weights of admissible candidates. -/
def candidateWeights (N : ℕ) : Finset ℝ :=
  (admissibleCandidates N).image reciprocalWeight

/-- The maximum reciprocal weight, with the value `0` only in the degenerate
case where the candidate collection is empty. Since the candidates form a
finite set, this definition avoids any unbounded or empty `sSup`. -/
noncomputable def maximumWeight (N : ℕ) : ℝ :=
  if h : (candidateWeights N).Nonempty then
    (candidateWeights N).max' h
  else
    0

/-- The normalized finite extremal quantity asked for in the source. -/
noncomputable def normalizedMaximum (N : ℕ) : ℝ :=
  maximumWeight N / Real.log N

/-- A qualitative formalization of the recorded resolution: the normalized
finite maximum converges to a positive constant. The source additionally
records that this constant is explicit and approximately `0.618`; that
formula is not supplied in the frozen source, so it is deliberately not
invented here. -/
theorem qualitative_resolution :
    ∃ c : ℝ, 0 < c ∧
      Tendsto normalizedMaximum atTop (𝓝 c) := by
  sorry Erdos858
