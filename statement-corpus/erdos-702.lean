/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $k\geq 4$. If $\mathcal{F}$ is a family of subsets of $\{1,\ldots,n\}$ with $\lvert A\rvert=k$ for all $A\in \mathcal{F}$ and $\lvert \mathcal{F}\rvert >\binom{n-2}{k-2}$ then there are $A,B\in\mathcal{F}$ such that $\lvert A\cap B\rvert=1$.

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#702 : [Er75f,p.108] [Er76b,p.186] [Er81] [Er82e] combinatorics A conjecture of Erdős and Sós. Katona (unpublished) proved this when $k=4$, and Frankl [Fr77] proved this for all $k\geq 4$. See also [703] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 22 January 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #702, https://www.erdosproblems.com/702, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable JoshuaB Working on formalising parclytaxel Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos702

/-- A family of subsets of `Fin n`, represented as a finite set of finite subsets,
with every member having cardinality `k`. -/
def UniformFamily (n k : ℕ) (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝓕, A.card = k

/-- `HasSingletonIntersection n 𝓕` means that two members of the family
have intersection of cardinality one. -/
def HasSingletonIntersection (n : ℕ) (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

/-- A proved control: the singleton family containing the whole four-element
set is uniform, but has no pair with intersection of cardinality one. -/
theorem singleton_control :
    UniformFamily 4 4
        ({(Finset.univ : Finset (Fin 4))} : Finset (Finset (Fin 4))) ∧
      ¬ HasSingletonIntersection 4
        ({(Finset.univ : Finset (Fin 4))} : Finset (Finset (Fin 4))) := by
  constructor
  · intro A hA
    have hEq : A = (Finset.univ : Finset (Fin 4)) := by
      simpa using hA
    rw [hEq]
    simp
  · rintro ⟨A, hA, B, hB, hAB⟩
    have hAeq : A = (Finset.univ : Finset (Fin 4)) := by
      simpa using hA
    have hBeq : B = (Finset.univ : Finset (Fin 4)) := by
      simpa using hB
    rw [hAeq, hBeq] at hAB
    simpa using hAB

/-- Erdős--Sós' theorem in the finite-set model `Fin n`: if `k ≥ 4`, every
member of `𝓕` has cardinality `k`, and the family is larger than
`Nat.choose (n - 2) (k - 2)`, then two members have intersection of
cardinality one.

The source records this result as proved by Frankl for all `k ≥ 4`.
The formal derivation remains an explicit gap here. -/
theorem erdos_sos
    (n k : ℕ) (𝓕 : Finset (Finset (Fin n)))
    (hk : 4 ≤ k)
    (huniform : UniformFamily n k 𝓕)
    (hcard : 𝓕.card > Nat.choose (n - 2) (k - 2)) :
    HasSingletonIntersection n 𝓕 := by
  sorry

#print axioms singleton_control

end Erdos702
