/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $g(k)$ be the smallest integer (if any such exists) such that any $g(k)$ points in $\mathbb{R}^2$ contains an empty convex $k$-gon (i.e. with no point in the interior). Does $g(k)$ exist? If so, estimate $g(k)$.

NODE n001-resolution (resolution), VERBATIM:
#216 : [Er78c] [Er81] [Er82e] [Er83c] [Er97e] geometry | convex A variant of the 'happy ending' problem [107] , which asks for the same without the 'no point in the interior' restriction. Erdős observed $g(4)=5$ (as with the happy ending problem) but Harborth [Ha78] showed that $g(5)=10$. Nicolás [Ni07] and Gerken [Ge08] independently showed that $g(6)$ exists. Horton [Ho83] showed that $g(n)$ does not exist for $n\geq 7$. Heule and Scheucher [HeSc24] have proved that $g(6)=30$. This problem is #2 in Ramsey Theory in the graphs problem collection. Additional thanks to : Boris Alexeev and Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 30 December 2025. ( View history ) View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #216, https://www.erdosproblems.com/216, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A381776 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Is anyone working on this? parclytaxel Working on formalising parclytaxel Previous Next <!-- Redirect links and searches when in dual vi
-/






import Mathlib
open Classical

-- @category research solved




open Classical Filter

namespace Erdos216

/-- The Euclidean plane used in the problem, represented with its Euclidean metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- `EmptyConvexK P k` means that the finite point set `P` contains `k` points in
convex position whose convex hull has no point of `P` in its interior. -/
def EmptyConvexK (P : Finset Plane) (k : ℕ) : Prop :=
  ∃ v : Fin k → Plane,
    Function.Injective v ∧
    (∀ i, v i ∈ P) ∧
    (∀ i, v i ∉ convexHull ℝ (Set.range
      (fun j : {j : Fin k // j ≠ i} => v j.1))) ∧
    (∀ p ∈ P, p ∉ interior (convexHull ℝ (Set.range v)))

/-- `GoodBound k n` says that every finite set of at least `n` points in the
Euclidean plane contains an empty convex `k`-gon. -/
def GoodBound (k n : ℕ) : Prop :=
  ∀ P : Finset Plane, P.card ≥ n → EmptyConvexK P k

/-- `IsSmallestBound k n` formalizes that `n` is the smallest integer with the
property defining `g(k)`. -/
def IsSmallestBound (k n : ℕ) : Prop :=
  GoodBound k n ∧ ∀ m < n, ¬ GoodBound k m

/-- The zero-gon predicate has the expected degenerate witness; this is a
proved control showing that the formal predicate is not definitionally empty. -/
theorem emptyConvexK_zero : EmptyConvexK (∅ : Finset Plane) 0 := by
  refine ⟨fun i => Fin.elim0 i, ?_, ?_, ?_, ?_⟩
  · intro a
    exact Fin.elim0 a
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · simp

/-- The smallest bound, when it exists, is unique. -/
theorem smallest_unique {k n m : ℕ}
    (hn : IsSmallestBound k n) (hm : IsSmallestBound k m) : n = m := by
  apply Nat.le_antisymm
  · by_contra h
    have hmn : m < n := by omega
    exact hn.2 m hmn hm.1
  · by_contra h
    have hnm : n < m := by omega
    exact hm.2 n hnm hn.1

/-- Erdős's and the happy-ending value `g(4) = 5`, formalized using the
geometric definition above. The mathematical extremal argument remains to be
supplied here. -/
theorem g_four : IsSmallestBound 4 5 := by
  sorry

/-- Harborth's value `g(5) = 10`, formalized using the geometric definition
above. The mathematical extremal argument remains to be supplied here. -/
theorem g_five : IsSmallestBound 5 10 := by
  sorry

/-- Heule and Scheucher's theorem `g(6) = 30`, formalized using the geometric
definition above. The mathematical proof remains to be supplied here. -/
theorem g_six : IsSmallestBound 6 30 := by
  sorry

/-- The source's statement that `g(6)` exists, as a direct consequence of its
identified value. -/
theorem g_six_exists : ∃ n, IsSmallestBound 6 n := by
  refine ⟨30, g_six⟩

/-- Horton's nonexistence result: for every `k ≥ 7`, no finite integer is a
bound forcing an empty convex `k`-gon. The geometric construction proving this
remains to be supplied here. -/
theorem no_bound_of_seven_le {k : ℕ} (hk : 7 ≤ k) :
    ¬ ∃ n, GoodBound k n := by
  sorry

/-- Mapping of the source clause: “Horton [Ho83] showed that $g(n)$ does not
exist for $n\geq 7$” is represented as the absence of any `GoodBound k n`
when `7 ≤ k`, rather than as a smallest-bound assertion. -/
theorem g_does_not_exist_for_large_k :
    ∀ k : ℕ, 7 ≤ k → ¬ ∃ n, GoodBound k n := by
  intro k hk
  exact no_bound_of_seven_le hk

#print axioms emptyConvexK_zero
#print axioms smallest_unique
#print axioms g_six_exists

end Erdos216
