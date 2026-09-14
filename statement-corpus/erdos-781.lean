/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(k)$ be the minimal $n$ such that any $2$-colouring of $\{1,\ldots,n\}$ contains a monochromatic $k$-term descending wave: a sequence $x_1<\cdots <x_k$ such that, for $1<j<k$,\[x_j \geq \frac{x_{j+1}+x_{j-1}}{2}.\]Estimate $f(k)$. In particular is it true that $f(k)=k^2-k+1$ for all $k$?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#781 : [BEF90] additive combinatorics A question of Brown, Erdős, and Freedman [BEF90] , who proved\[k^2-k+1\leq f(k) \leq \frac{k^3-4k+9}{3}.\]Resolved by Alon and Spencer [AlSp89] who proved that in fact \(f(k) \gg k^3\). Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #781, https://www.erdosproblems.com/781, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research solved







open Classical Filter

namespace Erdos781

/-- A two-colouring of the first `n` natural numbers. -/
def Coloring (n : ℕ) := Fin n → Bool

/-- A `k`-term descending wave in a colouring, with the source inequality
for every interior term. -/
def IsDescendingWave (c : Coloring n) (s : Fin k → Fin n) : Prop :=
  (∀ i j : Fin k, i < j → s i < s j) ∧
    (∀ i j : Fin k, c (s i) = c (s j)) ∧
    (∀ (j : ℕ) (hj : 1 < j) (hjk : j + 1 < k),
      ((s ⟨j, by omega⟩).val : ℝ) ≥
        (((s ⟨j + 1, by omega⟩).val : ℝ) +
          (s ⟨j - 1, by omega).val : ℝ) / 2)

/-- The assertion that every two-colouring of `{0, ..., n - 1}` contains
a monochromatic `k`-term descending wave. -/
def EveryColoringHasWave (n k : ℕ) : Prop :=
  ∀ c : Coloring n, ∃ s : Fin k → Fin n, IsDescendingWave c s

/-- Existence of a value satisfying the defining property of the minimal
wave length threshold. This is the finiteness assertion implicit in the
source's definition of `f`; its proof is not reproduced here. -/
theorem exists_wave_threshold (k : ℕ) : ∃ n : ℕ, EveryColoringHasWave n k := by
  sorry

/-- The minimal `n` such that every two-colouring of the first `n` numbers
contains a `k`-term descending wave. It is defined by `Nat.find` from the
finiteness assertion above. -/
noncomputable def f (k : ℕ) : ℕ :=
  Nat.find (exists_wave_threshold k)

/-- Sanity control: every colouring of a singleton contains a one-term wave. -/
theorem singleton_control : EveryColoringHasWave 1 1 := by
  intro c
  refine ⟨fun _ => 0, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have h : i = j := Subsingleton.elim _ _
    exact (lt_irrefl i) (h ▸ hij)
  · intro i j
    rfl
  · intro j hj hjk
    omega

/-- Sanity control in the opposite direction: no colouring of the empty
set can contain even a one-term wave. -/
theorem empty_control : ¬ EveryColoringHasWave 0 1 := by
  intro h
  obtain ⟨s, hs⟩ := h (fun x => Fin.elim0 x)
  exact Fin.elim0 (s 0)

/-- The Brown--Erdős--Freedman bounds recorded in the resolution, interpreted
over natural numbers with the displayed subtraction and division truncated
as in Lean. The substantive combinatorial proof is left as an explicit gap. -/
theorem bef_bounds (k : ℕ) :
    k ^ 2 - k + 1 ≤ f k ∧ f k ≤ (k ^ 3 - 4 * k + 9) / 3 := by
  sorry

/-- The Alon--Spencer resolution, formalizing the notation `f(k) ≫ k^3`
as the existence of a positive real constant giving an eventual cubic lower
bound. The source supplies no constant or proof details here, so this
theorem records that literature result with an explicit honest gap. -/
theorem alon_spencer_cubic :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ k : ℕ in atTop, C * (k : ℝ) ^ 3 ≤ (f k : ℝ) := by
  sorry

/-- The source question asks whether `f(k) = k^2-k+1` for every `k`; the
resolution instead records cubic growth, so the question is settled negatively
in the stated asymptotic sense. The exact incompatibility proof from the
cubic result is not supplied here. -/
theorem quadratic_formula_question :
    ¬ (∀ k : ℕ, f k = k ^ 2 - k + 1) := by
  sorry

#print axioms singleton_control
#print axioms empty_control

end Erdos781
