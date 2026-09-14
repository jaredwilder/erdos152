/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $B\subseteq\mathbb{N}$ be an additive basis of order $k$ with $0\in B$. Is it true that for every $A\subseteq\mathbb{N}$ we have\[d_s(A+B)\geq \alpha+\frac{\alpha(1-\alpha)}{k},\]where $\alpha=d_s(A)$ and\[d_s(A) = \inf \frac{\lvert A\cap\{1,\ldots,N\}\rvert}{N}\]is the Schnirelmann density?
-/

/-
SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#35 : [Er56] number theory | additive basis Erdős [Er36c] proved this is true with $k$ replaced by $2k$ in the denominator (in a stronger form that only considers $A\cup (A+b)$ for some $b\in B$, see [38] ). Ruzsa has observed that this follows immediately from the stronger fact proved by Plünnecke [Pl70] that (under the same assumptions)\[d_S(A+B)\geq \alpha^{1-1/k}.\] Additional thanks to : Imre Ruzsa Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #35, https://www.erdosproblems.com/35, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes holyterror Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

import Mathlib

-- @category research open

namespace ErdosProblem35

/-- The sumset of two sets of natural numbers, written in the usual additive form. -/
def addSet (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, a + b = n}

/-- The literal Schnirelmann density from the source, using the infimum over positive
initial intervals. The use of `sInf` is intentional: it is the direct formal counterpart
of the source's displayed infimum. -/
noncomputable def schDensity (A : Set ℕ) : ℝ :=
  sInf {x : ℝ | ∃ N : ℕ, 0 < N ∧
    x = ((Finset.Icc 1 N).filter (fun n => n ∈ A)).card / (N : ℝ)}

/-- `IsAdditiveBasis B k` means that every natural number is a sum of exactly `k`
members of `B`; the summands are indexed by `Fin k`. -/
def IsAdditiveBasis (B : Set ℕ) (k : ℕ) : Prop :=
  ∀ n : ℕ, ∃ f : Fin k → ℕ,
    (∀ i, f i ∈ B) ∧ ∑ i, f i = n

/-- The source's target question, read literally: for every additive basis `B` of order
`k` with `0 ∈ B`, and every `A`, the displayed lower bound holds with
`alpha = schDensity A`. This is recorded as a proposition rather than asserted as proved,
because the frozen entry records only the weaker `2k` result and the stronger Plünnecke
bound. -/
def ErdosQuestion35 : Prop :=
  ∀ (k : ℕ) (B : Set ℕ), 0 < k → IsAdditiveBasis B k → 0 ∈ B →
    ∀ A : Set ℕ,
      schDensity (addSet A B) ≥
        schDensity A + schDensity A * (1 - schDensity A) / (k : ℝ)

/-- The weaker result recorded in the resolution, with `2k` in place of `k`. -/
def ErdősWeakerBound : Prop :=
  ∀ (k : ℕ) (B : Set ℕ), 0 < k → IsAdditiveBasis B k → 0 ∈ B →
    ∀ A : Set ℕ,
      schDensity (addSet A B) ≥
        schDensity A + schDensity A * (1 - schDensity A) / ((2 * k : ℕ) : ℝ)

/-- The stronger bound attributed in the resolution to Plünnecke. -/
def PlunneckeBound : Prop :=
  ∀ (k : ℕ) (B : Set ℕ), 0 < k → IsAdditiveBasis B k → 0 ∈ B →
    ∀ A : Set ℕ,
      schDensity (addSet A B) ≥
        schDensity A ^ (1 - (1 : ℝ) / (k : ℝ))

/-- A proved control exercising the additive-basis definition: the full set of natural
numbers is an additive basis of order one. -/
theorem univ_isAdditiveBasis_one : IsAdditiveBasis Set.univ 1 := by
  intro n
  refine ⟨fun _ => n, ?_, ?_⟩
  · intro i
    simp
  · simp

/-- A proved control for the sumset definition: adding the full set of natural numbers
to itself gives the full set of natural numbers. -/
theorem addSet_univ_univ : addSet Set.univ Set.univ = Set.univ := by
  ext n
  constructor
  · intro _
    simp
  · intro _
    refine ⟨0, by simp, n, by simp, by simp⟩

#print axioms univ_isAdditiveBasis_one
#print axioms addSet_univ_univ

end ErdosProblem35