/-
# Erdős problem #687 — Jacobsthal-type covering of an initial interval  (**OPEN**, $1000 prize)

## The question (verbatim from the frozen source, node `n000-question`)

> Let $Y(x)$ be the maximal $y$ such that there exists a choice of congruence classes $a_p$ for
> all primes $p\leq x$ such that every integer in $[1,y]$ is congruent to at least one of the
> $a_p\pmod{p}$.
>
> Give good estimates for $Y(x)$. In particular, can one prove that $Y(x)=o(x^2)$ or even
> $Y(x)\ll x^{1+o(1)}$?

## The resolution node (verbatim, node `n001-resolution`)

> This function (associated with Jacobsthal) is closely related to the problem of gaps between
> primes (see [4] ). The best known upper bound is due to Iwaniec \cite{Iw78},
> \[Y(x) \ll x^2.\]
> The best lower bound is due to Ford, Green, Konyagin, Maynard, and Tao \cite{FGKMT18},
> \[Y(x) \gg x\frac{\log x\log\log\log x}{\log\log x},\]
> improving on a previous bound of Rankin \cite{Ra38}. Maier and Pomerance have conjectured that
> $Y(x)\ll x(\log x)^{2+o(1)}$. In \cite{Er80} he writes 'It is not clear who first formulated
> this problem - probably many of us did it independently. I offer the maximum of \$1000 dollars
> and $1/2$ my total savings for clearing up of this problem.' In \cite{Er80} Erdős also asks
> about a weaker variant in which all except $o(y/\log y)$ of the integers in $[1,y]$ are
> congruent to at least one of the $a_p\pmod{p}$, and in particular asks if the answer is very
> different. See also [688] and [689] . A more general Jacobsthal function is the focus of
> [970] .

## What is formalized here — and what is deliberately NOT

**This problem is OPEN.**  Accordingly this file states the QUESTION and asserts no answer to it.
`Erdos687.Question` (`Y(x) = o(x²)`) and `Erdos687.QuestionSharp` (`Y(x) ≪ x^{1+o(1)}`) are
`def ... : Prop`, never theorems.  Nothing here proves, disproves, or presupposes either one.
There is no `erdos_687_resolution`.  The Maier–Pomerance conjecture is likewise a `def`, because
a conjecture is not a result.

What *is* stated as a `theorem` (each with `sorry`, each named after the author the source
credits) is only what the resolution node records as **known**:

* `iwaniec_upper_bound` — `Y(x) ≪ x²`  (Iwaniec, `Iw78`).
* `ford_green_konyagin_maynard_tao_lower_bound` — `Y(x) ≫ x·log x·log log log x / log log x`
  (`FGKMT18`).
* `coverSet_bddAbove` / `Y_lt_primorial` — the standard well-definedness fact (see below).
  Not part of the open problem; it is what makes `Y` a number at all.

⛔ **Rankin's bound is NOT formalized, on purpose.**  The source says only that `FGKMT18` improves
"a previous bound of Rankin \cite{Ra38}" and never states its shape.  Writing down a formula for
it would be inventing a citation, so this file records the omission instead of guessing.

## The junk-value trap, named

`Y x` is `sSup (CoverSet x)` where `CoverSet x = {y | Covers x y}`.  In Mathlib `sSup` on `ℕ`
returns `0` on a set that is **empty or unbounded above** — a silent junk value that would make
`Y` look small exactly where it is large.  Both halves are addressed explicitly:

* **Empty:** ruled out by `coverSet_nonempty`, which is PROVED here (`0 ∈ CoverSet x` always,
  because `Finset.Icc 1 0 = ∅` and the covering condition is vacuous).
* **Unbounded:** ruled out by `coverSet_bddAbove` (stated, `sorry`).  This is *not* the open
  problem and it is not deep: by CRT the covered set is periodic with period the primorial
  `∏_{p ≤ x} p`, and the number of residues mod that primorial missed by all the classes is
  `∏_{p ≤ x} (p-1) > 0`, so some integer in every window of that length is uncovered; hence
  `Y x < ∏_{p ≤ x} p` (`Y_lt_primorial`).  Every downstream statement about `Y` is meaningful
  only under this fact, which is why it is stated rather than assumed silently.
* Consequently `Y 1 = 0` below is a **real** zero (proved from the definition), not the junk one,
  and `Y 2 = 1` is proved with an explicit `BddAbove` witness rather than by trusting `sSup`.

## Conventions the source leaves unstated (each one NAMED, with the reading taken)

* **`a_p` ranges over `ℕ`, not `ZMod p`.**  A choice function `a : ℕ → ℕ` picks a natural-number
  representative for each prime; `n ≡ a p [MOD p]` (`Nat.ModEq`) then says `n` lies in the class
  `a_p mod p`.  This is equivalent to a choice in `ZMod p` — every residue class has a natural
  representative and `Nat.ModEq` only sees `a p % p` — and it avoids a dependent family
  `Π p, ZMod p`, which would force `Fintype`/`NeZero` side conditions into every statement.
  `a` is total on `ℕ`; its values outside `primesLE x` are irrelevant and unconstrained.
* **`p` ranges over ALL primes `≤ x`, including `p = 2`.**  The source says "all primes
  $p\leq x$" with no parity restriction, so `2` is in.  Formalized as `Nat.primesLE x`
  (Mathlib: `Nat.primesLE n = Nat.primesBelow (n+1)`, membership `Nat.mem_primesLE :
  p ∈ primesLE n ↔ p ≤ n ∧ p.Prime`).  ⛔ *Not* `primesBelow x`, which is the strict `p < x`.
* **`[1,y]` is INCLUSIVE at both ends**, and is an interval of integers: `Finset.Icc 1 y`.  For
  `y = 0` it is empty, which is what makes `0` always coverable and gives `Y` its floor.
* **`x` is a natural number.**  The source writes `Y(x)` for real `x`, but the condition depends
  on `x` only through the finite set of primes `≤ x`, so `Y` on the reals is the step function
  `Y(⌊x⌋)`.  Taking `x : ℕ` loses nothing and keeps `Nat.primesLE` usable directly.
* **"maximal `y`" is a supremum over the set of admissible `y`**, `sSup {y | Covers x y}`, not a
  `max` over choices of `(a_p)`: the choice is existentially quantified *inside* `Covers`, so a
  different `(a_p)` may witness each `y`.  Since `Covers x` is downward closed in `y`
  (`covers_mono_y`, PROVED) and bounded (above), this supremum is attained and agrees with
  "maximal".
* **`≪` (Vinogradov)** is read as: `∃ C > 0` with the inequality holding for all sufficiently
  large `x` (`∀ᶠ x in atTop`).  `≫` is the same with the inequality reversed.
* **`o(x²)`** is unfolded by hand as `∀ ε > 0, ∀ᶠ x in atTop, Y x ≤ ε·x²` rather than via
  `Asymptotics.IsLittleO`, so that the statement is readable without unfolding filter machinery;
  the two are equivalent for a nonnegative function.
* **`x^{1+o(1)}`** is unfolded as `∀ ε > 0, ∃ C > 0, ∀ᶠ x, Y x ≤ C·x^{1+ε}` — note the quantifier
  order: `C` may depend on `ε`.  ⛔ There is no Mathlib little-o that lives inside an exponent.
  `(log x)^{2+o(1)}` in Maier–Pomerance is unfolded the same way.
* **`log`** is the natural logarithm `Real.log`; `log log log x` is `Real.log (Real.log
  (Real.log x))`.  These are ill-behaved for small `x`, which is exactly why every asymptotic
  statement is guarded by `∀ᶠ x in atTop`.
* **The weak variant** ("all except `o(y/log y)` of the integers in `[1,y]`") is formalized with
  an explicit tolerance constant `c > 0` (`AlmostCovers x y c`) instead of a nested little-o,
  and Erdős's "is the answer very different?" is read as: *for every tolerance, almost-covering
  reaches intervals longer than `Y x` by any constant factor* (`QuestionWeakVariant`).  This is
  ONE precise reading of an informally posed question, and it is a `def : Prop` — open, not
  asserted.  ⛔ No `Y*` supremum is defined: `AlmostCovers x · c` is **not** known to be downward
  closed in `y` nor bounded, so a `Nat.sSup` there would be a live junk-value hazard rather than
  a definition.

## Mathlib used

`Nat.Prime`, `Nat.primesLE` / `Nat.primesBelow` (with `Nat.mem_primesLE`), `Nat.ModEq`,
`Finset.Icc`, `Set.ncard`, `sSup`/`csSup_le`/`le_csSup`/`csSup_le_csSup` on `ℕ`,
`Filter.atTop`/`Filter.Eventually`, `Real.log`, `Real.rpow`.
-/

-- @category research open
-- @AMS 11
-- Category vocabulary and AMS tagging adopted from the formal-conjectures corpus
-- (509 files, measured 2026-08-28). Written as a comment rather than the corpus
-- attribute form, so this artifact still elaborates standalone, outside their project.









import Mathlib
namespace Erdos687

open Filter

/-! ### The covering condition -/

/-- `Covers x y` : *there exists a choice of congruence classes `a_p` for all primes `p ≤ x` such
that every integer in `[1,y]` is congruent to at least one of the `a_p (mod p)`.*

* `a : ℕ → ℕ` picks a natural representative of the class `a_p`; values at non-primes and at
  primes `> x` are unconstrained and never used.
* `Nat.primesLE x` is `{p | p ≤ x ∧ p.Prime}`; `p = 2` is included.
* `Finset.Icc 1 y` is `[1,y]` inclusive; it is empty when `y = 0`. -/
def Covers (x y : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ n ∈ Finset.Icc 1 y, ∃ p ∈ Nat.primesLE x, n ≡ a p [MOD p]

/-- The set of interval lengths achievable at parameter `x`. -/
def CoverSet (x : ℕ) : Set ℕ := {y | Covers x y}

/-- `Y x` — *the maximal `y` such that ...*, as a supremum over `CoverSet x`.

⛔ `sSup` on `ℕ` returns the junk value `0` when the set is empty or unbounded above.  Neither
happens: `coverSet_nonempty` (PROVED) and `coverSet_bddAbove` (stated).  See the file header. -/
noncomputable def Y (x : ℕ) : ℕ := sSup (CoverSet x)

/-! ### Anti-vacuity controls — PROVED (no `sorry`), exercising the definitions above -/

/-- Length `0` is always coverable: `[1,0]` is empty, so the condition is vacuous.
This is what keeps `CoverSet x` nonempty, and hence keeps `Y x = 0` from being the junk value. -/
theorem covers_zero (x : ℕ) : Covers x 0 := by
  refine ⟨fun _ => 0, ?_⟩
  intro n hn
  rw [Finset.mem_Icc] at hn
  exact absurd hn (by omega)

/-- `CoverSet x` is never empty. -/
theorem coverSet_nonempty (x : ℕ) : (CoverSet x).Nonempty :=
  ⟨0, covers_zero x⟩

/-- `Covers x ·` is downward closed in the interval length: the same choice `(a_p)` works. -/
theorem covers_mono_y {x y y' : ℕ} (h : y' ≤ y) (hy : Covers x y) : Covers x y' := by
  obtain ⟨a, ha⟩ := hy
  refine ⟨a, fun n hn => ha n ?_⟩
  rw [Finset.mem_Icc] at hn ⊢
  exact ⟨hn.1, le_trans hn.2 h⟩

/-- `Covers · y` is monotone in `x`: more primes are available, the same choice still works. -/
theorem covers_mono_x {x x' y : ℕ} (h : x ≤ x') (hy : Covers x y) : Covers x' y := by
  obtain ⟨a, ha⟩ := hy
  refine ⟨a, fun n hn => ?_⟩
  obtain ⟨p, hp, hpn⟩ := ha n hn
  rw [Nat.mem_primesLE] at hp
  exact ⟨p, Nat.mem_primesLE.mpr ⟨le_trans hp.1 h, hp.2⟩, hpn⟩

/-- With no primes available (`x = 1`) nothing at all can be covered, so `Y 1 = 0` — and this
zero is a genuine value of the supremum, not `Nat.sSup`'s junk value on an empty set. -/
theorem not_covers_one {y : ℕ} (hy : 0 < y) : ¬ Covers 1 y := by
  rintro ⟨a, ha⟩
  obtain ⟨p, hp, -⟩ := ha 1 (Finset.mem_Icc.mpr ⟨le_refl 1, hy⟩)
  rw [Nat.mem_primesLE] at hp
  have := hp.2.two_le
  omega

/-- **PROVED small case.** `Y 1 = 0`: there are no primes `≤ 1`. -/
theorem Y_one : Y 1 = 0 := by
  refine le_antisymm (csSup_le (coverSet_nonempty 1) ?_) (Nat.zero_le _)
  intro b hb
  by_contra hcon
  exact not_covers_one (Nat.pos_of_ne_zero (by omega)) hb

/-- With only the prime `2` available, `[1,2]` cannot be covered: `1` and `2` lie in different
classes mod `2`, and a single class `a_2` cannot contain both. -/
theorem not_covers_two_two : ¬ Covers 2 2 := by
  rintro ⟨a, ha⟩
  obtain ⟨p, hp, h1⟩ := ha 1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  obtain ⟨q, hq, h2⟩ := ha 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  rw [Nat.mem_primesLE] at hp hq
  have hp2 : p = 2 := le_antisymm hp.1 hp.2.two_le
  have hq2 : q = 2 := le_antisymm hq.1 hq.2.two_le
  subst hp2; subst hq2
  have : (1 : ℕ) % 2 = 2 % 2 := h1.trans h2.symm
  omega

/-- `[1,1]` is coverable at `x = 2`: take `a_2 = 1`. -/
theorem covers_two_one : Covers 2 1 := by
  refine ⟨fun _ => 1, fun n hn => ⟨2, Nat.mem_primesLE.mpr ⟨le_refl 2, Nat.prime_two⟩, ?_⟩⟩
  rw [Finset.mem_Icc] at hn
  have : n = 1 := le_antisymm hn.2 hn.1
  subst this
  rfl

/-- `CoverSet 2` is bounded above by `1` — an explicit `BddAbove` witness, so `Y_two` below does
not have to trust `sSup` on a set whose boundedness is unproved. -/
theorem coverSet_two_bddAbove : BddAbove (CoverSet 2) := by
  refine ⟨1, fun b hb => ?_⟩
  by_contra hcon
  exact not_covers_two_two (covers_mono_y (by omega) hb)

/-- **PROVED small case, the first nontrivial value.** `Y 2 = 1`.

This is the computed case that pins the conventions down: it is `1` (not `2`) because `[1,y]` is
inclusive and `p = 2` is an admissible prime, and it is a real supremum, taken over a set proved
bounded by `coverSet_two_bddAbove`. -/
theorem Y_two : Y 2 = 1 := by
  refine le_antisymm (csSup_le (coverSet_nonempty 2) ?_) ?_
  · intro b hb
    by_contra hcon
    exact not_covers_two_two (covers_mono_y (by omega) hb)
  · exact le_csSup coverSet_two_bddAbove covers_two_one

/-- **PROVED: monotonicity of `Y` in `x`**, given the (stated) boundedness at the larger
parameter.  Enlarging `x` only adds primes to choose from. -/
theorem Y_mono_of_bddAbove {x x' : ℕ} (h : x ≤ x') (hb : BddAbove (CoverSet x')) :
    Y x ≤ Y x' :=
  csSup_le_csSup hb (coverSet_nonempty x) (fun _ hy => covers_mono_x h hy)

/-! ### Well-definedness: the facts that keep `Y` away from the junk value.
These are standard (CRT), NOT the open problem. -/

/-- `Y x < ∏_{p ≤ x} p`.  By CRT the set of covered residues is periodic modulo the primorial,
and `∏_{p ≤ x}(p-1) > 0` residues escape every choice of classes, so an uncovered integer occurs
in every window of that length.  (For `x ≤ 1` the empty product is `1` and `Y x = 0`.) -/
theorem Y_lt_primorial (x : ℕ) : Y x < ∏ p ∈ Nat.primesLE x, p := by
  sorry

/-- Hence `CoverSet x` is bounded above, so `Y x = sSup (CoverSet x)` is the genuine maximum and
never `Nat.sSup`'s unbounded-set junk value `0`. -/
theorem coverSet_bddAbove (x : ℕ) : BddAbove (CoverSet x) := by
  sorry

/-! ### THE QUESTION.  Both forms are OPEN; neither is asserted here. -/

/-- **Erdős #687, first form (OPEN).**  *"Can one prove that $Y(x)=o(x^2)$?"*

Unfolded: for every `ε > 0`, eventually `Y x ≤ ε·x²`.

This is a `def`, not a `theorem`: the problem is open and this file takes no position on it. -/
def Question : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, (Y x : ℝ) ≤ ε * (x : ℝ) ^ 2

/-- **Erdős #687, sharper form (OPEN).**  *"or even $Y(x)\ll x^{1+o(1)}$?"*

Unfolded: for every `ε > 0` there is a constant `C > 0` (allowed to depend on `ε`) with
eventually `Y x ≤ C·x^{1+ε}`.  Again a `def`, not a `theorem`. -/
def QuestionSharp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
    (Y x : ℝ) ≤ C * (x : ℝ) ^ ((1 : ℝ) + ε)

/-- **The Maier–Pomerance conjecture (OPEN).**  *"Maier and Pomerance have conjectured that
$Y(x)\ll x(\log x)^{2+o(1)}$."*

A conjecture recorded by the source, hence a `def : Prop`, never a sorried theorem. -/
def MaierPomeranceConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
    (Y x : ℝ) ≤ C * (x : ℝ) * (Real.log x) ^ ((2 : ℝ) + ε)

/-! ### The weak variant Erdős also asks about (OPEN) -/

/-- The number of integers of `[1,y]` left uncovered by the choice `a`. -/
noncomputable def uncoveredCount (x y : ℕ) (a : ℕ → ℕ) : ℕ :=
  {n : ℕ | 1 ≤ n ∧ n ≤ y ∧ ∀ p ∈ Nat.primesLE x, ¬ n ≡ a p [MOD p]}.ncard

/-- PROVED control on the weak-variant definition: nothing is uncovered in the empty interval. -/
theorem uncoveredCount_zero (x : ℕ) (a : ℕ → ℕ) : uncoveredCount x 0 a = 0 := by
  have h : {n : ℕ | 1 ≤ n ∧ n ≤ 0 ∧ ∀ p ∈ Nat.primesLE x, ¬ n ≡ a p [MOD p]} = (∅ : Set ℕ) := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    omega
  unfold uncoveredCount
  rw [h, Set.ncard_empty]

/-- `AlmostCovers x y c` : *all except at most `c·y/log y` of the integers in `[1,y]` are
congruent to at least one of the `a_p (mod p)`.*  The little-o of the source is unfolded into an
explicit tolerance constant `c`. -/
def AlmostCovers (x y : ℕ) (c : ℝ) : Prop :=
  ∃ a : ℕ → ℕ, (uncoveredCount x y a : ℝ) ≤ c * (y : ℝ) / Real.log y

/-- **The weak variant (OPEN).**  *"Erdős also asks about a weaker variant in which all except
$o(y/\log y)$ of the integers in $[1,y]$ are congruent to at least one of the $a_p\pmod{p}$, and
in particular asks if the answer is very different."*

Reading taken (NAMED, one of several possible): "very different" is read as *unboundedly larger* —
for every tolerance `c > 0` and every factor `K`, almost-covering eventually reaches intervals at
least `K` times longer than the exactly-coverable `Y x`.  A `def : Prop`; nothing here asserts it
either way, and no weak analogue of `Y` is defined (see the header: no boundedness is known for
the weak covering set, so a `Nat.sSup` there would be a junk-value hazard). -/
def QuestionWeakVariant : Prop :=
  ∀ c : ℝ, 0 < c → ∀ K : ℝ, ∀ᶠ x : ℕ in atTop,
    ∃ y : ℕ, K * (Y x : ℝ) ≤ (y : ℝ) ∧ AlmostCovers x y c

/-! ### Bounds the source records as KNOWN.  Each is `sorry`: stated, not proved here.

⛔ Rankin `Ra38` is deliberately absent: the source records only that `FGKMT18` improves it, never
its shape, and inventing a formula would be inventing a citation. -/

/-- **Best known upper bound (Iwaniec, `Iw78`).**  `Y(x) ≪ x²`.

⛔ This does NOT answer `Question`, which asks for the strictly stronger `Y(x) = o(x²)`. -/
theorem iwaniec_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, (Y x : ℝ) ≤ C * (x : ℝ) ^ 2 := by
  sorry

/-- **Best known lower bound (Ford, Green, Konyagin, Maynard, Tao, `FGKMT18`).**
\[Y(x) \gg x\frac{\log x\log\log\log x}{\log\log x}.\]
Improves an earlier bound of Rankin (`Ra38`, shape not recorded by the source). -/
theorem ford_green_konyagin_maynard_tao_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      C * (x : ℝ) * (Real.log x * Real.log (Real.log (Real.log x)))
          / Real.log (Real.log x) ≤ (Y x : ℝ) := by
  sorry

/-- Recorded so the two forms of the question are not read as independent: the sharper
`x^{1+o(1)}` form implies the `o(x²)` form. -/
theorem questionSharp_imp_question : QuestionSharp → Question := by
  sorry

/-- The Maier–Pomerance conjecture, if true, would answer the first form of the question. -/
theorem maierPomerance_imp_question : MaierPomeranceConjecture → Question := by
  sorry

end Erdos687

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos687.covers_zero
#print axioms Erdos687.coverSet_nonempty
#print axioms Erdos687.covers_mono_y
#print axioms Erdos687.covers_mono_x
#print axioms Erdos687.not_covers_one
#print axioms Erdos687.Y_one
#print axioms Erdos687.not_covers_two_two
#print axioms Erdos687.covers_two_one
#print axioms Erdos687.coverSet_two_bddAbove
#print axioms Erdos687.Y_two
#print axioms Erdos687.Y_mono_of_bddAbove
#print axioms Erdos687.Y_lt_primorial
#print axioms Erdos687.coverSet_bddAbove
#print axioms Erdos687.uncoveredCount_zero
#print axioms Erdos687.iwaniec_upper_bound
#print axioms Erdos687.ford_green_konyagin_maynard_tao_lower_bound
#print axioms Erdos687.questionSharp_imp_question
#print axioms Erdos687.maierPomerance_imp_question
