/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $(A_i)$ be a family of countably infinite sets such that $\lvert A_i\cap A_j\rvert \neq 2$ for all $i\neq j$. Find the smallest cardinal $C$ such that $\cup A_i$ can always be coloured with at most $C$ colours so that no $A_i$ is monochromatic.
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#603 : [Er87] combinatorics | set theory A problem of Komjáth. If instead we have $\lvert A_i\cap A_j\rvert \neq 1$ then Komjáth showed that this is possible with at most $\aleph_0$ colours. GPT 5.4 Pro (prompted by Chojecki) proved there is no uniform bound on such $C$: for every cardinal $C$ there is a family of countably infinite sets $(A_i)$ such that $\lvert A_i\cap A_j\rvert \neq 2$ for all $i\neq j$, and in any colouring of $\cup A_i$ with $C$ colours some $A_i$ is monochromatic. Indeed, by the Erdős-Rado theorem , if $\kappa$ is the successor of $2^C$, any $C$-colouring of the edges of the complete graph on $\kappa$ vertices contains a monochromatic countably infinite complete graph, and hence we can take $(A_i)$ to be the collection of all countably infinite complete graphs (since any two such intersect in either countably infinite or $\binom{n}{2}$ many edges for some finite $n$, and in particular never intersect exactly twice). Additional thanks to : Stijn Cambie, Przemek Chojecki, LouisD, and Desmond Weisenberg Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (14) Proof claims (0) More information and links This page was last edited 06 July 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #603, https://www.erdosproblems.com/603, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos603

/-- A family is admissible when every member is countably infinite and distinct
members do not have intersection of cardinality exactly two. -/
def IsAdmissible (α I : Type) (A : I → Set α) : Prop :=
  (∀ i, Set.Countable (A i) ∧ Set.Infinite (A i)) ∧
    (∀ i j, i ≠ j →
      Cardinal.mk {x : α // x ∈ A i ∩ A j} ≠ (2 : Cardinal))

/-- A set is monochromatic for a coloring when all of its elements receive
the same color. -/
def Monochromatic {α β : Type} (γ : α → β) (s : Set α) : Prop :=
  ∃ c, ∀ x, x ∈ s → γ x = c

/-- A coloring avoids the family when no member of the family is monochromatic. -/
def HasAvoidingColoring (α I : Type) (A : I → Set α) : Prop :=
  ∃ (β : Type) (γ : α → β), ∀ i, ¬ Monochromatic γ (A i)

/-- Every coloring using a color type of cardinality at most `C` has a
monochromatic member of the family. -/
def EveryColoringFails (C : Cardinal) (α I : Type) (A : I → Set α) : Prop :=
  ∀ (β : Type), Cardinal.mk β ≤ C →
    ∀ γ : α → β, ∃ i, Monochromatic γ (A i)

/-- A concrete one-member family used as an anti-vacuity control. -/
def oneFamily : Fin 1 → Set ℕ :=
  fun _ => Set.univ

/-- The concrete control family is admissible: its sole member is countably
infinite, and the intersection condition is vacuous because there are no
distinct indices. -/
theorem oneFamily_admissible :
    IsAdmissible ℕ (Fin 1) oneFamily := by
  constructor
  · intro i
    simp [oneFamily]
  · intro i j hij
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    exact (hij (hi.trans hj.symm)).elim

/-- The concrete control family does admit an avoiding coloring, namely parity
with two colors; thus the definitions do not make every family automatically
uncolorable. -/
theorem oneFamily_has_avoiding_coloring :
    HasAvoidingColoring ℕ (Fin 1) oneFamily := by
  refine ⟨Bool, (fun n : ℕ => n % 2 == 0), ?_⟩
  intro i hmono
  rcases hmono with ⟨c, hc⟩
  have h0 := hc 0 (by simp [oneFamily])
  have h1 := hc 1 (by simp [oneFamily])
  have htrue : (true : Bool) = c := by
    simpa using h0
  have hfalse : c = (false : Bool) := by
    simpa using h1.symm
  have : (true : Bool) = false := htrue.trans hfalse
  cases this

/-- Formalization of the resolution of Erdos problem 603.

The source says that for every cardinal `C` there is an admissible family for
which every coloring using at most `C` colors has a monochromatic member.
The remaining gap is the construction from the Erdős--Rado theorem described
in the resolution: take countably infinite monochromatic complete subgraphs
and regard their edge sets as the family. -/
theorem no_uniform_bound :
    ∀ C : Cardinal,
      ∃ (α I : Type) (A : I → Set α),
        IsAdmissible α I A ∧ EveryColoringFails C α I A := by
  sorry

#print axioms oneFamily_admissible
#print axioms oneFamily_has_avoiding_coloring

end Erdos603
