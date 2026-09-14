/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $C>0$ be arbitrary. Is it true that, if $n$ is sufficiently large depending on $C$, then in any $2$-colouring of $\binom{\{2,\ldots,n\}}{2}$ there exists some $X\subseteq \{2,\ldots,n\}$ such that $\binom{X}{2}$ is monochromatic and\[\sum_{x\in X}\frac{1}{\log x}\geq C?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#191 : [ErGr79,p.333] [ErGr80,p.17] [Er81,p.15] [Er82e,p.78] combinatorics | ramsey theory The answer is yes, which was proved by Rödl [Ro03] . In the same article Rödl also proved a lower bound for this problem, constructing, for all $n$, a $2$-colouring of $\binom{\{2,\ldots,n\}}{2}$ such that if $X\subseteq \{2,\ldots,n\}$ is such that $\binom{X}{2}$ is monochromatic then\[\sum_{x\in X}\frac{1}{\log x}\ll \log\log\log n.\]In the same paper Rödl proves that the answer to the main problem is negative if we consider $3$-colourings. This bound is best possible, as proved by Conlon, Fox, and Sudakov [CFS13] , who proved that, if $n$ is sufficiently large, then in any $2$-colouring of $\binom{\{2,\ldots,n\}}{2}$ there exists some $X\subseteq \{2,\ldots,n\}$ such that $\binom{X}{2}$ is monochromatic and\[\sum_{x\in X}\frac{1}{\log x}\geq 2^{-8}\log\log\log n.\] Additional thanks to : Mehtaab Sawhney and Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 08 February 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #191, https://www.erdosproblems.com/191, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos191

/-- The finite vertex set `{2, ..., n}` appearing in the source problem. -/
def vertexSet (n : ℕ) : Finset ℕ :=
  Finset.Icc 2 n

/-- A colouring is represented by a Boolean value assigned to every finite set;
only its values on two-element subsets are used below. -/
def Coloring :=
  Finset ℕ → Bool

/-- `IsMonochromatic n c X` says that `X` lies in `{2, ..., n}` and all of
its two-element subsets have the same colour under `c`. -/
def IsMonochromatic (n : ℕ) (c : Coloring) (X : Finset ℕ) : Prop :=
  X ⊆ vertexSet n ∧
    ∃ b : Bool, ∀ p ∈ X.powerset, p.card = 2 → c p = b

/-- The weighted size of a finite set used in the Erdős problem. -/
def weightedSize (X : Finset ℕ) : ℝ :=
  ∑ x ∈ X, 1 / Real.log (x : ℝ)

/-- A singleton is monochromatic for every colouring once it belongs to the
allowed vertex set. This is a proved control exercising the formalized
monochromaticity predicate. -/
theorem singleton_monochromatic_control
    (n : ℕ) (c : Coloring) (hn : 2 ≤ n) :
    IsMonochromatic n c ({2} : Finset ℕ) := by
  refine ⟨?_, ⟨c {2}, ?_⟩⟩
  · intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    simp [vertexSet, hn]
  · intro p hp hcard
    have hsub : p ⊆ ({2} : Finset ℕ) :=
      Finset.mem_powerset.mp hp
    have hle := Finset.card_le_card hsub
    have hle' : p.card ≤ 1 := by
      simpa using hle
    omega

/-- The weighted size of the singleton `{2}` is positive, providing a
nondegenerate numerical control for the reciprocal-logarithmic weight. -/
theorem singleton_weight_positive_control :
    0 < weightedSize ({2} : Finset ℕ) := by
  rw [show weightedSize ({2} : Finset ℕ) = 1 / Real.log (2 : ℝ) by
    simp [weightedSize]]
  have hlog : 0 < Real.log (2 : ℝ) := by
    exact Real.log_pos (by norm_num)
  positivity

/-- Formalization of the affirmative answer to Erdős Problem #191:
for every positive real `C`, all sufficiently large `n` have the property
that every two-colouring admits a monochromatic set of weighted size at least
`C`. The proof of the deep Rödl theorem remains to be supplied; the statement
uses finite sets to represent subsets of `{2, ..., n}` and Boolean values to
represent the two colours. -/
theorem erdos_191 :
    ∀ C : ℝ, 0 < C →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ c : Coloring, ∃ X : Finset ℕ,
          IsMonochromatic n c X ∧ weightedSize X ≥ C := by
  sorry Erdos191

#print axioms Erdos191.singleton_monochromatic_control
#print axioms Erdos191.singleton_weight_positive_control
