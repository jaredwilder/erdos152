/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is there some constant $C>0$ such that any graph on $n$ vertices with $\geq Cr^2n$ edges contains a subdivision of $K_r$?

NODE n001-resolution (resolution), VERBATIM:
#718 : [Er81] graph theory A conjecture of Erdős, Hajnal, and Mader. Dirac [Di60] proved that every graph on $n$ vertices with at least $2n-2$ edges contains a subdivision of $K_4$, and conjectured that $3n-5$ edges forces a subdivision of $K_5$. Mader [Ma67] proved that $\geq 2^{\binom{r}{2}}n$ edges suffices. The answer is yes, proved independently by Komlós and Szemerédi [KoSz96] and Bollobás and Thomason [BoTh96] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #718, https://www.erdosproblems.com/718, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos718

/-- The number of edges of a finite simple graph, represented by the cardinality of
its edge set. -/
def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Fintype.card G.edgeSet

/-- `IsPath G xs a b` says that `xs` is a simple path in `G` from `a` to `b`.
The list is written with its two endpoints displayed explicitly. -/
def IsPath {V : Type} (G : SimpleGraph V) (xs : List V) (a b : V) : Prop :=
  ∃ ys : List V,
    xs = a :: ys ++ [b] ∧
      xs.Nodup ∧
        xs.Chain' G.Adj

/-- `IsKSubdivision G r` says that `G` contains a subdivision of the complete
graph on `r` branch vertices.  The function `b` gives the distinct branch
vertices, and for each `i < j`, `p i j` is a simple path from `b i` to `b j`.
The final two conditions require that branch vertices do not occur internally
on these paths and that distinct paths have disjoint interiors. -/
def IsKSubdivision {V : Type} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ b : Fin r → V,
    Function.Injective b ∧
      ∃ p : Fin r → Fin r → List V,
        ∀ i j : Fin r,
          i < j →
            IsPath G (p i j) (b i) (b j) ∧
              (∀ x : V, x ∈ p i j → x = b i ∨ x = b j ∨ ∀ k : Fin r, x ≠ b k) ∧
                (∀ k l : Fin r, k < l →
                  ∀ x : V,
                    x ∈ p i j →
                      x ∈ p k l →
                        (x = b i ∨ x = b j) ∧ (x = b k ∨ x = b l))

/-- A non-vacuous syntactic control on the subdivision predicate: every graph
on one vertex contains the subdivision of `K₁`, since there are no pairs of
branch vertices whose connecting paths need to be supplied. -/
theorem subdivision_one_control (G : SimpleGraph (Fin 1)) :
    IsKSubdivision G 1 := by
  refine ⟨fun _ => 0, ?_, fun _ _ => [], ?_⟩
  · intro i j h
    exact Subsingleton.elim _ _
  · intro i j hij
    exfalso
    exact hij (Subsingleton.elim _ _)

/-- Erdős problem 718, as resolved by Komlós--Szemerédi and independently by
Bollobás--Thomason.

The source asks whether there is a constant `C > 0` such that every graph on
`n` vertices with at least `C r² n` edges contains a subdivision of `K_r`.
Here `edgeCount G` is compared with the real quantity
`C * r² * n`, and `IsKSubdivision` is the explicit branch-vertex-and-path
formalization above.  The proof of the deep extremal graph theorem remains an
external mathematical input. -/
theorem erdos_718 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n r : ℕ) (G : SimpleGraph (Fin n)),
        C * (r : ℝ) ^ 2 * (n : ℝ) ≤ (edgeCount G : ℝ) →
          IsKSubdivision G r := by
  sorry Erdos718
