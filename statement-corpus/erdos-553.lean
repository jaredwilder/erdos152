/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $R(3,3,n)$ denote the smallest integer $m$ such that if we $3$-colour the edges of $K_m$ then there is either a monochromatic triangle in one of the first two colours or a monochromatic $K_n$ in the third colour. Define $R(3,n)$ similarly but with two colours. Show that\[\frac{R(3,3,n)}{R(3,n)}\to \infty\]as $n\to \infty$.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#553 : [ErSo80] graph theory | ramsey theory A problem of Erdős and Sós. This was solved by Alon and Rödl [AlRo05] , who in fact show that\[R(3,3,n)\asymp n^3(\log n)^{O(1)}\](recalling that Shearer [Sh83] showed $R(3,n) \ll n^2/\log n$). This problem is #22 in Ramsey Theory in the graphs problem collection. See also [925] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #553, https://www.erdosproblems.com/553, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A000791 , possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical
open Filter

-- @category research solved





open Classical Filter

namespace Erdos553

/-- An edge of the complete graph on `Fin m`, represented by a two-element finset. -/
def Edge (m : ℕ) := {e : Finset (Fin m) // e.card = 2}

/-- A `k`-edge-colouring of the complete graph on `Fin m`. -/
def Coloring (m k : ℕ) := Edge m → Fin k

/-- `HasClique k t c col` says that the colouring `c` has a monochromatic
`t`-clique of colour `col`. -/
def HasClique (k t : ℕ) {m : ℕ} (c : Coloring m k) (col : Fin k) : Prop :=
  ∃ S : Finset (Fin m), S.card = t ∧
    ∀ e : Edge m, e.1 ⊆ S → c e = col

/-- Every colouring has a monochromatic clique of size zero. -/
theorem hasClique_zero {m k : ℕ} (c : Coloring m k) (col : Fin k) :
    HasClique k 0 c col := by
  refine ⟨∅, by simp, ?_⟩
  intro e he
  have heq : e.1 = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    have hx' : x ∈ (∅ : Finset (Fin m)) := he hx
    exact Finset.not_mem_empty x hx'
  have hp : e.1.card = 2 := e.2
  rw [heq] at hp
  simp at hp

/-- The three-colour Ramsey property for the mixed problem: every colouring
has a triangle in one of the first two colours or a clique of size `n` in
the third colour. -/
def ThreeColourProperty (n m : ℕ) : Prop :=
  ∀ c : Coloring m 3,
    (∃ col : Fin 3, col.val < 2 ∧ HasClique 3 3 c col) ∨
      HasClique 3 n c 2

/-- The usual two-colour Ramsey property for a triangle versus an `n`-clique. -/
def TwoColourProperty (n m : ℕ) : Prop :=
  ∀ c : Coloring m 2,
    (∃ col : Fin 2, HasClique 2 3 c col) ∨
      HasClique 2 n c 1

/-- Existence of the finite Ramsey number in the three-colour formulation.
This is the finite Ramsey theorem specialized to the two forbidden targets
used here; its proof is not reproduced in this formalization. -/
theorem threeColour_exists (n : ℕ) :
    ∃ m, ThreeColourProperty n m := by
  sorry

/-- Existence of the finite two-colour Ramsey number in the triangle versus
clique formulation; this is the finite Ramsey theorem in the relevant
special case. -/
theorem twoColour_exists (n : ℕ) :
    ∃ m, TwoColourProperty n m := by
  sorry

/-- `R33 n` is the smallest order whose every three-colouring has a
monochromatic triangle in one of the first two colours or a monochromatic
`n`-clique in the third colour. -/
noncomputable def R33 (n : ℕ) : ℕ :=
  Nat.find (threeColour_exists n)

/-- `R2 n` is the smallest order whose every two-colouring has a
monochromatic triangle or a monochromatic `n`-clique in the other colour. -/
noncomputable def R2 (n : ℕ) : ℕ :=
  Nat.find (twoColour_exists n)

/-- The definitions have the expected degenerate control value at `n = 0`;
this also shows that neither Ramsey predicate is silently always false. -/
theorem ramsey_zero_control : R33 0 = 0 ∧ R2 0 = 0 := by
  constructor
  · apply Nat.find_eq_zero
    intro c
    exact Or.inr (hasClique_zero c 2)
  · apply Nat.find_eq_zero
    intro c
    exact Or.inr (hasClique_zero c 1)

/-- The source clause is “Show that `R(3,3,n) / R(3,n) → ∞` as `n → ∞`”.
Here `R33` is the three-colour quantity and `R2` is the two-colour
quantity, so the ratio is oriented exactly as in the source. The resolution
records that Alon and Rödl proved this, with the stronger estimate
`R(3,3,n) ≍ n^3 (log n)^{O(1)}` together with Shearer's upper bound for
`R(3,n)`. The asymptotic derivation from those literature bounds remains
formalized here as an explicit gap. -/
theorem ramsey_ratio_tendsto :
    Tendsto (fun n : ℕ => (R33 n : ℝ) / (R2 n : ℝ)) atTop atTop := by
  sorry Erdos553
