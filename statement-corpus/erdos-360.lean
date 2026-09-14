/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(n)$ be minimal such that $\{1,\ldots,n-1\}$ can be partitioned into $f(n)$ classes so that $n$ cannot be expressed as a sum of distinct elements from the same class. How fast does $f(n)$ grow?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#360 : [ErGr80,p.59] number theory Alon and Erdős [AlEr96] proved that $f(n) = n^{1/3+o(1)}$, and more precisely\[\frac{n^{1/3}}{(\log n)^{4/3}}\ll f(n) \ll \frac{n^{1/3}}{(\log n)^{1/3}}(\log\log n)^{1/3}.\]Vu [Vu07] improved the lower bound to\[f(n) \gg \frac{n^{1/3}}{\log n}.\]Conlon, Fox, and Pham [CFP21] determined the order of growth of $f(n)$ up to a multiplicative constant, proving\[f(n) \asymp \frac{n^{1/3}(n/\phi(n))}{(\log n)^{1/3}(\log\log n)^{2/3}}.\] Additional thanks to : Noga Alon Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #360, https://www.erdosproblems.com/360, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos360

/-- The finite set `{1, ..., n - 1}` appearing in the source question. -/
def ground (n : ℕ) : Finset ℕ :=
  (Finset.range n).erase 0

/-- `Admissible n k` says that the elements of `ground n` are assigned to `k`
classes, with no monochromatic set of distinct elements summing to `n`.
The harmless `n = 0` clause records that the source question concerns positive
integers and prevents the empty sum from creating an endpoint artefact. -/
def Admissible (n k : ℕ) : Prop :=
  n = 0 ∨
    ∃ c : {x // x ∈ ground n} → Fin k,
      ∀ s : Finset ℕ,
        s ⊆ ground n →
        s.sum id = n →
        ¬ ∃ a : Fin k, ∀ x ∈ s, c ⟨x, ‹x ∈ ground n›⟩ = a

/-- The candidates used to define the minimum.  The upper cut `k ≤ n + 1`
makes the defining set bounded above; this is safe because `n + 1` singleton
classes always suffice for positive `n`. -/
def Candidates (n : ℕ) : Set ℕ :=
  {k | Admissible n k ∧ k ≤ n + 1}

/-- The extremal number in the source question, defined as a natural infimum.
The boundedness and nonemptiness of `Candidates n` are recorded below, so this
definition does not rely on the junk value of an empty or uncontrolled infimum. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf (Candidates n)

/-- A proved anti-vacuity control: at the zero endpoint, one class is an
admissible candidate by the explicit endpoint clause in `Admissible`. -/
theorem control_zero : 1 ∈ Candidates 0 := by
  simp [Candidates, Admissible]

/-- The singleton-colouring construction supplies an admissible candidate for
every positive parameter.  The remaining proof is elementary finitary
bookkeeping about monochromatic finite sums. -/
theorem admissible_upper (n : ℕ) : Admissible n (n + 1) := by
  sorry

/-- The candidate set is nonempty.  This is the nonemptiness control needed
when interpreting the natural infimum defining `f`; its proof uses
`control_zero` at zero and `admissible_upper` otherwise. -/
theorem candidates_nonempty (n : ℕ) : (Candidates n).Nonempty := by
  sorry

/-- The candidate set is bounded above by `n + 1`, so the `sInf` in the
definition of `f` is controlled rather than a junk value. -/
theorem candidates_bddAbove (n : ℕ) : BddAbove (Candidates n) := by
  refine ⟨n + 1, ?_⟩
  intro k hk
  exact hk.2

/-- The scale appearing in the resolution node, with Euler's totient
function `Nat.totient`. -/
noncomputable def growthScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 3 : ℝ) *
    ((n : ℝ) / (Nat.totient n : ℝ)) /
      ((Real.log n) ^ (1 / 3 : ℝ) *
        (Real.log (Real.log n)) ^ (2 / 3 : ℝ))

/-- A precise two-sided multiplicative formulation of the source's statement
that the order of growth of `f` is
`n^(1/3) (n / phi(n)) / ((log n)^(1/3) (log log n)^(2/3))`. -/
def GrowthClaim : Prop :=
  ∃ c C : ℝ, ∃ N : ℕ,
    0 < c ∧ c ≤ C ∧
      ∀ n : ℕ, N ≤ n →
        c * growthScale n ≤ (f n : ℝ) ∧
          (f n : ℝ) ≤ C * growthScale n

/-- Resolution of Erdős Problem 360, as recorded in node `n001-resolution`.
The asymptotic theorem is imported from the cited work of Conlon, Fox, and
Pham; its formal proof is not supplied here. -/
theorem resolution : GrowthClaim := by
  sorry

#print axioms control_zero

end Erdos360
