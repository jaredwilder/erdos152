/-
# Erdős problem 157 — formalization of the RESOLUTION

SOURCE (frozen, the only authority):
  question   (n000-question):   "Does there exist an infinite Sidon set which is an asymptotic
                                 basis of order 3?"
  resolution (n001-resolution): "Yes, as shown by Pilatte \cite{Pi23}."
  reference  [Pi23] Pilatte, C., *A solution to the Erdős-Sárközy-Sós problem on asymptotic
                    Sidon bases of order 3*. arXiv:2303.09659 (2023).

We formalize the RESOLUTION (the affirmative answer) as an existence theorem. Proof is `sorry`.

--------------------------------------------------------------------------------
CONVENTIONS NAMED (the source leaves all three unstated)
--------------------------------------------------------------------------------

1. AMBIENT SET. Sidon sets / asymptotic bases of order 3 in the Erdős–Sárközy–Sós problem live
   in ℕ (equivalently the nonnegative integers). We take `Set ℕ`.

2. SIDON. We use the SUM formulation (`IsSidon` below):
      ∀ a b c d ∈ A, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)
   i.e. all pairwise sums with repetition allowed are distinct up to order — the classical
   B₂-set definition.
   * Sum vs difference: in ℤ (hence in ℕ, where subtraction is only partial and the difference
     form is awkward) the two are EQUIVALENT, since a + b = c + d ↔ a − c = d − b. The genuine
     edge case is whether the DEGENERATE pairs a = b are included. We INCLUDE them: our
     quantifiers range over all a b c d ∈ A with no distinctness hypothesis, so a + a = c + d
     forces c = d = a. This is the STRONGER reading; the weaker reading (only pairs a < b must
     have distinct sums, permitting a + b = 2c) is NOT what B₂/Sidon means and would weaken the
     theorem, since Sidon-ness sits in existential position here.
   * A Sidon set may contain 0 under this definition; we do not exclude it, as the classical
     statement does not.

3. INFINITE. `Set.Infinite A` (Mathlib), i.e. `¬ A.Finite`. Note it is implied by the basis
   property but we state it anyway, exactly as the source does.

4. ASYMPTOTIC BASIS OF ORDER 3. We use:
      ∃ N, ∀ n ≥ N, ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a + b + c = n
   "Asymptotic" = the representation is required only for all SUFFICIENTLY LARGE n (finitely
   many exceptions permitted), as opposed to a plain basis of order 3 where EVERY n must be so
   represented. EXACTLY three summands, repetitions allowed, distinctness of a, b, c NOT
   required — this is the standard convention for "basis of order h". Requiring exactly three
   summands is the stronger reading than "at most three"; we take the stronger one.

--------------------------------------------------------------------------------
MATHLIB NEAR-MISSES CHECKED (and deliberately NOT used)
--------------------------------------------------------------------------------
* `schnirelmannDensity` (`Mathlib/Combinatorics/Schnirelmann.lean`) — the Schnirelmann-density
  route to "basis of order h" is a DIFFERENT notion: positive Schnirelmann density gives a
  basis (no exceptions allowed, and it constrains ALL initial segments). "Asymptotic" basis is
  about a natural-density/cofinite tail condition. Using Schnirelmann here would be wrong in
  both directions. RECORDED as the trap.
* `ThreeAPFree` / `ThreeGPFree` (`Mathlib/Combinatorics/Additive/AP/Three/Defs.lean`):
  `a + c = b + b → a = b`. This is exactly the DEGENERATE case of the Sidon condition and is
  strictly WEAKER than Sidon. Not usable as a definition of Sidon.
* `AddDissociated` (`Mathlib/Combinatorics/Additive/Dissociation.lean`): all FINITE SUBSET sums
  distinct. Strictly STRONGER than Sidon and a different notion.
* `Finset.addEnergy` (`Mathlib/Combinatorics/Additive/Energy.lean`): Sidon ⇔ minimal additive
  energy, but only for finsets; no `Set`-level Sidon predicate exists in Mathlib.
* Mathlib has NO `Sidon` predicate and NO `asymptotic basis` predicate (grepped): both are
  defined locally below.
-/
-- @category research solved
-- @AMS 11
-- Category vocabulary and AMS tagging adopted from the
-- formal-conjectures corpus (509 files, measured 2026-08-28). Written as a comment
-- rather than the corpus attribute form, so this artifact still elaborates
-- standalone, outside their project.


import Mathlib
namespace Erdos157

/-- A set `A ⊆ ℕ` is a **Sidon set** (a `B₂` set) if all pairwise sums of elements of `A`,
repetitions allowed, are distinct up to the order of the two summands. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A set `A ⊆ ℕ` is an **asymptotic basis of order 3** if every sufficiently large natural
number is a sum of exactly three (not necessarily distinct) elements of `A`. -/
def IsAsymptoticBasisOfOrder3 (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a + b + c = n

/-- **Erdős problem 157 (Erdős–Sárközy–Sós), resolution.**

Question: "Does there exist an infinite Sidon set which is an asymptotic basis of order 3?"
Resolution: "Yes, as shown by Pilatte [Pi23]."

There exists an infinite Sidon set of natural numbers that is an asymptotic basis of order 3. -/
theorem exists_infinite_sidon_asymptotic_basis_order_three :
    ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧ IsAsymptoticBasisOfOrder3 A := by
  sorry

/-! ### Sanity checks that the definitions bite (no `sorry`, kernel-checked) -/

/-- The Sidon condition as stated does forbid the degenerate collision `a + a = c + d`
with `c ≠ d`: it is not vacuous on the diagonal. -/
example (A : Set ℕ) (h : IsSidon A) (a c d : ℕ) (ha : a ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hsum : a + a = c + d) : c = d := by
  rcases h a ha a ha c hc d hd hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- "Asymptotic" is doing work: a plain basis of order 3 (every `n`) is an asymptotic basis,
but not conversely. This direction is the easy one and shows the tail quantifier is weaker. -/
example (A : Set ℕ) (h : ∀ n : ℕ, ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a + b + c = n) :
    IsAsymptoticBasisOfOrder3 A :=
  ⟨0, fun n _ => h n⟩

end Erdos157

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos157.exists_infinite_sidon_asymptotic_basis_order_three
