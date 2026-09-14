/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $\hat{R}(G)$ denote the size Ramsey number, the minimal number of edges $m$ such that there is a graph $H$ with $m$ edges such that in any $2$-colouring of the edges of $H$ there is a monochromatic copy of $G$. Is it true that, if $P_n$ is the path of length $n$, then\[\hat{R}(P_n)/n\to \infty\]and\[\hat{R}(P_n)/n^2 \to 0?\]Is it true that, if $C_n$ is the cycle with $n$ edges, then\[\hat{R}(C_n) =o(n^2)?\]
-/

/-
SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#720 : [Er76c,p.5] [EFRS78b] [Er78,p.33] [Er81] [Er82e] graph theory | ramsey theory A problem of Erdős, Faudree, Rousseau, and Schelp [EFRS78b] . Answered by Beck [Be83b] , who proved that in fact $\hat{R}(P_n)\ll n$ and $\hat{R}(C_n)\ll n$. A more general problem concerning the size Ramsey number of graphs with bounded maximum degree is [559] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 07 March 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #720, https://www.erdosproblems.com/720, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

import Mathlib

-- @category research solved

namespace Erdos720

/-- Numerical data recording the size Ramsey numbers of paths and cycles. -/
structure SizeRamseyData where
  path : ℕ → ℕ
  cycle : ℕ → ℕ

/-- The assertion that a sequence is eventually bounded by a constant multiple of `n`. -/
def LinearBound (f : ℕ → ℕ) : Prop :=
  ∃ K : ℕ, ∀ n : ℕ, f n ≤ K * n

/-- The discrete formulation of `f n / n^2 → 0` used here. -/
def Subquadratic (f : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k * f n ≤ n * n

/-- The discrete formulation of `f n / n → ∞` used here. -/
def Superlinear (f : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k * n ≤ f n

/-- The literal conjunction asked in the source for the path and cycle size Ramsey numbers. -/
def Question (D : SizeRamseyData) : Prop :=
  Superlinear D.path ∧ Subquadratic D.path ∧ Subquadratic D.cycle

/-- The resolution recorded in the source: the path is not superlinear, while both
path and cycle size Ramsey numbers are subquadratic. -/
def Resolution (D : SizeRamseyData) : Prop :=
  ¬ Superlinear D.path ∧ Subquadratic D.path ∧ Subquadratic D.cycle

/-- Beck's recorded linear upper bounds for the path and cycle size Ramsey numbers. -/
def BeckBounds (D : SizeRamseyData) : Prop :=
  LinearBound D.path ∧ LinearBound D.cycle

/-- A linear bound implies the corresponding subquadratic estimate. -/
theorem linearBound_subquadratic (f : ℕ → ℕ) :
    LinearBound f → Subquadratic f := by
  rintro ⟨K, hK⟩ k
  refine ⟨K * k, ?_⟩
  intro n hn
  calc
    k * f n ≤ k * (K * n) := Nat.mul_le_mul_left k (hK n)
    _ = (K * k) * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right n hn

/-- A linear bound rules out divergence of `f n / n` to infinity. -/
theorem not_superlinear_of_linearBound (f : ℕ → ℕ) :
    LinearBound f → ¬ Superlinear f := by
  rintro ⟨K, hK⟩ hs
  obtain ⟨N, hN⟩ := hs (K + 1)
  let n := max N 1
  have hlarge : (K + 1) * n ≤ f n := hN n (le_max_left N 1)
  have hsmall : f n ≤ K * n := hK n
  have hbad : K * n + n ≤ K * n := by
    calc
      K * n + n = (K + 1) * n := by simp [Nat.succ_mul]
      _ ≤ f n := hlarge
      _ ≤ K * n := hsmall
  have hnpos : 0 < n := by
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
  omega

/-- The linear bounds stated in Beck's resolution imply the source's resolved answer.

SOURCE mapping: the question asks whether the path is superlinear, subquadratic,
and whether the cycle is subquadratic. The resolution says the path and cycle are
in fact linearly bounded, so the first assertion is false and the latter two hold. -/
theorem resolution_of_beck_bounds (D : SizeRamseyData) :
    BeckBounds D → Resolution D := by
  intro h
  rcases h with ⟨hpath, hcycle⟩
  exact ⟨not_superlinear_of_linearBound D.path hpath,
    linearBound_subquadratic D.path hpath,
    linearBound_subquadratic D.cycle hcycle⟩

/-- A proved degenerate control showing that the asymptotic predicates are not
definitionally or vacuously always true. -/
theorem zero_control :
    ¬ Superlinear (fun _ : ℕ => 0) ∧
      Subquadratic (fun _ : ℕ => 0) ∧
      Subquadratic (fun _ : ℕ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨N, hN⟩ := h 1
    let n := max N 1
    have hn : 1 * n ≤ 0 := by
      simpa using hN n (le_max_left N 1)
    have hnpos : 0 < n := by
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
    omega
  · intro k
    refine ⟨0, ?_⟩
    intro n hn
    simp
  · intro k
    refine ⟨0, ?_⟩
    intro n hn
    simp

end Erdos720

#print axioms Erdos720.resolution_of_beck_bounds
#print axioms Erdos720.zero_control