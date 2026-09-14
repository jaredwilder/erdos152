/-
Erdős problem 444 — the affirmative resolution (Erdős–Sárközy).

SOURCE (frozen, byte-exact, sha256 d955fbb62686276e...):
  oracle/evidence/formalizer-sources/erdos/erdos-444.tex

  "Let $A\subseteq\mathbb{N}$ be infinite and $d_A(n)$ count the number of $a\in A$ which
   divide $n$. Is it true that, for every $k$,
     \limsup_{x\to\infty} \frac{\max_{n<x} d_A(n)}{(\sum_{n\in A\cap[1,x)} 1/n)^k} = \infty?
   The answer is yes, proved by Erdős and Sárközy."

READING NOTES (each choice defended against the source, nothing added, nothing dropped):

* `A` is an arbitrary `Set ℕ` and `hA : A.Infinite` is carried as a hypothesis, exactly as the
  source states it. No other hypothesis is imposed.

* `k` is bound OUTSIDE the limsup, as the source's "for every k, limsup ... = ∞" demands.

* `x` is taken to range over `ℕ`, not `ℝ`. Both `max_{n<x} d_A(n)` and `∑_{n ∈ A ∩ [1,x)} 1/n`
  depend on a real `x` only through the integers `< x`, i.e. both are step functions constant on
  `[m, m+1)`. Hence the limsup along real `x → ∞` and along natural `x → ∞` are the same value,
  and the ℕ-indexed statement is faithful (and no weaker).

* `d_A(n)` is `Set.ncard {a | a ∈ A ∧ a ∣ n}` — literally "the number of `a ∈ A` which divide `n`".
  Using `ncard` avoids a decidability hypothesis the source does not have.

* `max_{n<x}` is taken over `1 ≤ n < x` (`Finset.Ico 1 x`), i.e. ℕ = {1,2,3,...} as in the
  source, whose companion expression `A ∩ [1,x)` starts at 1. This matters: `n = 0` is divisible
  by every `a`, so `d_A(0)` would be infinite for infinite `A` and would make the numerator
  vacuously unbounded. `Finset.sup` on ℕ is the max, and is `0` on the empty range (`x ≤ 1`).

* The denominator sum uses `Set.indicator A (fun m => 1/m)` over `Finset.Ico 1 x`, which is
  precisely `∑_{n ∈ A ∩ [1,x)} 1/n`, again with no decidability hypothesis.

* "limsup = ∞" is stated in two equivalent, defensible ways:
    `erdos_444`        — the unbounded-above form: for every real `C`, the ratio exceeds `C`
                         frequently along `atTop` (`∃ᶠ x in atTop`). For a real-valued sequence
                         this is exactly `limsup = +∞`.
    `erdos_444_limsup` — the same claim as a literal `Filter.limsup ... = ⊤` in `EReal`.
  Both are stated; neither is derived from the other here.

* Small `x`: the denominator `(∑_{n ∈ A ∩ [1,x)} 1/n)^k` can be `0` (empty intersection). Lean's
  division makes the ratio `0` there rather than undefined/infinite. This does NOT weaken the
  claim: the conclusion is an existential over arbitrarily large `x`, and since `A` is infinite
  the sum is positive for all large `x`, so the junk-value region is never used to satisfy it.
  (If anything the convention makes the statement harder, never easier.)

Proof obligations are left as `sorry`; this file is a STATEMENT formalization, verified only to
elaborate against real Mathlib.
-/
-- @category research solved
-- @AMS 11
-- Category vocabulary and AMS tagging adopted from the
-- formal-conjectures corpus (509 files, measured 2026-08-28). Written as a comment
-- rather than the corpus attribute form, so this artifact still elaborates
-- standalone, outside their project.

import Mathlib

open Filter

namespace Erdos444

/-- `dA A n` is `d_A(n)`: the number of `a ∈ A` which divide `n`. -/
noncomputable def dA (A : Set ℕ) (n : ℕ) : ℕ := {a | a ∈ A ∧ a ∣ n}.ncard

/-- `maxD A x` is `max_{n < x} d_A(n)`, the max taken over `1 ≤ n < x`. -/
noncomputable def maxD (A : Set ℕ) (x : ℕ) : ℕ := (Finset.Ico 1 x).sup (dA A)

/-- `S A x` is `∑_{n ∈ A ∩ [1,x)} 1/n`. -/
noncomputable def S (A : Set ℕ) (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 x, A.indicator (fun m => (1 : ℝ) / m) n

/-- **Erdős 444 (Erdős–Sárközy).** For every infinite `A ⊆ ℕ` and every `k`,
`max_{n<x} d_A(n) / (∑_{n ∈ A ∩ [1,x)} 1/n)^k` is unbounded above as `x → ∞`,
i.e. its `limsup` is `∞`. -/
theorem erdos_444 (A : Set ℕ) (hA : A.Infinite) (k : ℕ) :
    ∀ C : ℝ, ∃ᶠ x : ℕ in atTop, C < (maxD A x : ℝ) / (S A x) ^ k := by
  sorry

/-- The same statement written literally as `limsup = ⊤` in `EReal`. -/
theorem erdos_444_limsup (A : Set ℕ) (hA : A.Infinite) (k : ℕ) :
    limsup (fun x : ℕ => (((maxD A x : ℝ) / (S A x) ^ k : ℝ) : EReal)) atTop = ⊤ := by
  sorry

/-! ### Anti-vacuity controls (PROVED, not part of the source)

A `sorry`-carrying statement elaborates whether or not its definitions say anything. The
lemmas below are fully proved and mention only this file's own definitions (`dA`, `maxD`, `S`),
so they are cheap machine-checked evidence that those definitions bite. -/

/-- Degenerate case: with no elements at all, no `a` divides anything. -/
-- @category test
theorem dA_empty (n : ℕ) : dA ∅ n = 0 := by
  simp [dA]

/-- Degenerate case fixing the `max_{n<x}` convention: the range `[1, 1)` is empty, so the
numerator is `Finset.sup` of nothing, i.e. `0` — NOT the junk value that `n = 0` would give
(see the reading note on `max_{n<x}`). -/
-- @category test
theorem maxD_one (A : Set ℕ) : maxD A 1 = 0 := by
  simp [maxD]

/-- Same degenerate range for the denominator: `∑_{n ∈ A ∩ [1,1)} 1/n = 0`. This is the
`S A x = 0` region the reading note calls out, exhibited rather than asserted. -/
-- @category test
theorem S_one (A : Set ℕ) : S A 1 = 0 := by
  simp [S]

/-- The denominator base is never negative, for any `A` and any `x`. This is the fact the
"small `x`" reading note silently leans on when it argues that Lean's division convention
makes the ratio `0` (and never a spuriously large negative-denominator value) on the
degenerate range. -/
-- @category test
theorem S_nonneg (A : Set ℕ) (x : ℕ) : 0 ≤ S A x := by
  refine Finset.sum_nonneg fun n _ => ?_
  refine Set.indicator_nonneg (fun m _ => ?_) n
  positivity

/-- `maxD` is monotone in the cutoff `x`: enlarging the range `[1, x)` can only enlarge the
maximum. Together with `S_nonneg` this is what makes the `limsup` statement about a genuine
ratio of a growing numerator and a nonnegative denominator. -/
-- @category test
theorem maxD_mono (A : Set ℕ) {x y : ℕ} (h : x ≤ y) : maxD A x ≤ maxD A y :=
  Finset.sup_mono (Finset.Ico_subset_Ico le_rfl h)

end Erdos444

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos444.erdos_444
#print axioms Erdos444.erdos_444_limsup
#print axioms Erdos444.dA_empty
#print axioms Erdos444.maxD_one
#print axioms Erdos444.S_one
#print axioms Erdos444.S_nonneg
#print axioms Erdos444.maxD_mono
