/-
# Erdős problem 1191 — formalization of an OPEN problem ($1000)

SOURCE (frozen, the only authority; both nodes of `entry-graph-erdos-1191.json` read):

  question (n000-question), verbatim:
    "Let $A\subset\mathbb{N}$ be an infinite Sidon set. Is it true that
     \[\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}(\log x)^{1/2}=0?\]
     Does there exist an infinite Sidon set $A$ such that
     \[\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}(\log x)^c>0\]
     for some $c>0$?"

  resolution (n001-resolution), verbatim:
    "Erd\H{o}s proved (see for example \cite{HaRo66}) that if $A$ is an infinite Sidon set then
     \[\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}(\log x)^{1/2}\leq c\]
     for some constant $c>0$. In \cite{Er80} he offered \$1000 'for clearing up the problems'
     raised by this; he may have meant for finding the optimal function $f$ such that
     \[\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}f(x)=0\]
     for all infinite Sidon sets $A$. The second question is a stronger form of [39]. See also
     [729] for the behaviour of the $\limsup$."

  references: [Er80] Erdős, *A survey of problems in combinatorial number theory*,
              Ann. Discrete Math. (1980), 89-115.
              [HaRo66] Halberstam and Roth, *Sequences. Vol. I* (1966).

STATUS: **OPEN**. Nothing below asserts an answer to either question. The two questions are
stated as `Question1` / `Question2`, each a `def ... : Prop`, deliberately NOT as sorried
theorems: a sorried theorem makes a guess indistinguishable from a result. The only sorried
theorem in this file is the bound the resolution node attributes to Erdős, which is a
published result and is named after him.

--------------------------------------------------------------------------------
CONVENTIONS NAMED (every one of these the source leaves unstated)
--------------------------------------------------------------------------------

1. SIDON. `IsSidon` below is COPIED VERBATIM from the sibling artifact `erdos-157.lean`, so
   the two files agree on the estate's definition of a Sidon set:
      ∀ a b c d ∈ A, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)
   i.e. the classical B₂ condition, sums with repetition allowed, degenerate pairs a = b
   INCLUDED. See `erdos-157.lean` for the sum-vs-difference and degenerate-pair discussion,
   which applies unchanged here.

2. AMBIENT SET. `A ⊆ ℕ`, as `Set ℕ`, matching the source's `A ⊂ ℕ` and the sibling.

3. THE COUNTING FUNCTION `|A ∩ [1,x]|`. Taken as `Set.ncard` of
      {n | n ∈ A ∧ 1 ≤ n ∧ (n : ℝ) ≤ x}
   * `Set.ncard`, not a `Finset.filter`, because `A` is an arbitrary (infinite, possibly
     undecidable) `Set ℕ`, so no `Finset.filter` is available without a `DecidablePred`
     hypothesis that the source does not have. Finiteness of the counted set is not assumed:
     it is PROVED below (`finite_countSet`), so `ncard` is not silently returning its junk
     value 0 on an infinite set.
   * The interval is `[1,x]`, CLOSED AT BOTH ENDS and starting at 1, exactly as written. So
     `0 ∈ A` is never counted. Our `IsSidon` (like the sibling's) permits `0 ∈ A`; whether the
     source's `ℕ` contains 0 is immaterial to the asymptotics but is pinned here anyway.
   * The upper end is a REAL cutoff `(n : ℝ) ≤ x`, not `n ≤ ⌊x⌋₊`; the two sets are equal, but
     the real form is the literal reading and needs no floor lemma to state.

4. `x → ∞` RANGES OVER THE REALS. `liminf ... (atTop : Filter ℝ)`, not over ℕ. The source
   writes `x^{1/2}` and `\log x`, which are real-variable expressions. (Over ℕ the liminf is
   the same number, because the counting function is a step function and the weight is
   continuous between jumps, but that is a lemma, not a definition, and is not claimed here.)

5. `x^{1/2}` is `Real.sqrt x`; `(\log x)^{1/2}` and `(\log x)^c` are `Real.rpow` powers of
   `Real.log x` (real exponent, since `c` in question 2 is an arbitrary positive real). Both
   questions are therefore instances of ONE weight `sidonWeight A c x`, at `c = 1/2` and at a
   general `c > 0`. This is a modelling choice made visible rather than hidden: it is what
   lets `Question1` and the Erdős bound be literally the same expression at `c = 1/2`.

6. QUANTIFIER ON QUESTION 1. "Let $A$ be an infinite Sidon set. Is it true that ... = 0?" is
   read as UNIVERSAL over all infinite Sidon `A`. The alternative (a claim about one fixed
   unnamed `A`) is not a proposition at all. The resolution node confirms this reading: it
   speaks of "all infinite Sidon sets $A$".

7. QUANTIFIER ON QUESTION 2. "Does there exist an infinite Sidon set $A$ such that ... > 0 for
   some $c>0$?" is read as `∃ A, ∃ c > 0`, with `c` chosen AFTER `A` (the `c` is inside the
   scope of the `A`). The reverse order (one `c` working for some `A`) is implied by it, so
   this is the weaker/faithful reading of an existence question.

8. THE CONSTANT IN THE ERDŐS BOUND. "≤ c for some constant $c>0$" is read as an ABSOLUTE
   constant, uniform over all infinite Sidon sets (`∃ C > 0, ∀ A, ...`). This is the stronger
   reading and is what "a constant" means in this literature; the weaker per-`A` reading is an
   immediate consequence, so nothing is lost by taking it.

9. THE $1000 PHRASE IS NOT FORMALIZED AS A CLAIM. "the optimal function $f$" has no stated
   optimality order (pointwise? up to constants? along a subsequence?), so `optimal` is NOT
   defined here. What IS definable is the property such an `f` must have, and that is
   `IsNullWeightForAllSidon f` below — a `def`, asserted of nothing.

--------------------------------------------------------------------------------
A LIMINF TRAP, NAMED (Mathlib-specific, affects how question 2 should be read)
--------------------------------------------------------------------------------
`Filter.liminf f l = sSup {a | ∀ᶠ x in l, a ≤ f x}` in a conditionally complete lattice. On ℝ
this is well behaved when `f` is eventually bounded, and `sidonWeight A c` is bounded below by
0. But if the weight were unbounded ABOVE along `atTop`, the supremum would be over an
unbounded set and Mathlib's `sSup` returns its junk value `0` — so a "true liminf = +∞" would
print as `0` and make `Question2` read FALSE for a set that satisfies the mathematician's
reading. `Question2'` below is the junk-free restatement ("eventually bounded below by a
positive constant"). **No equivalence between `Question2` and `Question2'` is asserted** — that
equivalence needs an upper bound on the weight, which is itself part of what is open.

--------------------------------------------------------------------------------
MATHLIB NEAR-MISSES CHECKED (and deliberately NOT used)
--------------------------------------------------------------------------------
Carried over from `erdos-157.lean`, re-checked here:
* `ThreeAPFree` (`Mathlib/Combinatorics/Additive/AP/Three/Defs.lean`): `a + c = b + b → a = b`
  is only the DEGENERATE case of Sidon, strictly weaker. Rejected.
* `AddDissociated` (`Mathlib/Combinatorics/Additive/Dissociation.lean`): all finite subset sums
  distinct — strictly STRONGER, a different notion. Rejected.
* `Finset.addEnergy` (`Mathlib/Combinatorics/Additive/Energy.lean`): Sidon ⇔ minimal additive
  energy, but Finset-only; there is no `Set`-level Sidon predicate in Mathlib. Rejected.
* `schnirelmannDensity` (`Mathlib/Combinatorics/Schnirelmann.lean`): an INFIMUM over all initial
  segments, not a liminf, and its positivity is STRICTLY STRONGER than a positive lower
  asymptotic density. It is also the wrong normalisation entirely here (`/n`, not `/√n`).
  Rejected — and Mathlib has NO asymptotic density for subsets of ℕ, so the liminf is written
  out by hand, as in the sibling `erdos-339.lean`.
* Mathlib has no `Sidon` predicate and no counting-function-with-real-cutoff; both are local.
-/
-- @category research open
-- @AMS 11
-- Category vocabulary and AMS tagging adopted from the
-- formal-conjectures corpus (509 files, measured 2026-08-28). Written as a comment
-- rather than the corpus attribute form, so this artifact still elaborates
-- standalone, outside their project.









import Mathlib
open Filter

namespace Erdos1191

/-- A set `A ⊆ ℕ` is a **Sidon set** (a `B₂` set) if all pairwise sums of elements of `A`,
repetitions allowed, are distinct up to the order of the two summands.

Copied verbatim from the sibling artifact `erdos-157.lean` so that the two files agree. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The set counted by `|A ∩ [1,x]|`: the elements of `A` lying in the closed real interval
`[1, x]`. Kept as a named definition so the finiteness lemma below can be about it. -/
def countSet (A : Set ℕ) (x : ℝ) : Set ℕ := {n | n ∈ A ∧ 1 ≤ n ∧ (n : ℝ) ≤ x}

/-- The counting function `|A ∩ [1,x]|`, as a `Set.ncard`. Finiteness of the underlying set is
proved (`finite_countSet`), so this is never `ncard`'s junk value on an infinite set. -/
noncomputable def countUpTo (A : Set ℕ) (x : ℝ) : ℕ := (countSet A x).ncard

/-- The weighted quantity whose `liminf` both questions ask about:
`(|A ∩ [1,x]| / x^{1/2}) · (log x)^c`, with `c` a real exponent.

Question 1 is this at `c = 1/2`; question 2 asks for some `c > 0`. -/
noncomputable def sidonWeight (A : Set ℕ) (c : ℝ) (x : ℝ) : ℝ :=
  (countUpTo A x : ℝ) / Real.sqrt x * Real.log x ^ c

/-! ### The two questions. Each is a `Prop`; neither is asserted. -/

/-- **Erdős problem 1191, FIRST QUESTION (OPEN).**

Source, verbatim: "Let $A\subset\mathbb{N}$ be an infinite Sidon set. Is it true that
$\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}(\log x)^{1/2}=0?$"

Read universally over infinite Sidon sets (convention 6). This `def` is the QUESTION; this
file does not assert it, nor its negation. -/
def Question1 : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsSidon A → liminf (sidonWeight A (1 / 2)) atTop = 0

/-- **Erdős problem 1191, SECOND QUESTION (OPEN).**

Source, verbatim: "Does there exist an infinite Sidon set $A$ such that
$\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}(\log x)^c>0$ for some $c>0$?"

Read as `∃ A, ∃ c > 0` (convention 7). Kept strictly separate from `Question1`: these are two
different questions, and an answer to one is not an answer to the other. This `def` is the
QUESTION; this file does not assert it, nor its negation. -/
def Question2 : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧ ∃ c : ℝ, 0 < c ∧ 0 < liminf (sidonWeight A c) atTop

/-- **Junk-free restatement of the second question** (see the liminf trap in the header):
"eventually bounded below by a positive constant" says what `liminf > 0` is meant to say,
without depending on Mathlib's `sSup` junk value when the weight is unbounded above.

⛔ No equivalence with `Question2` is asserted here; establishing one requires an upper bound
on the weight, which is part of what is open. Both are recorded so a reader can see which
reading a future answer settles. -/
def Question2' : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧ ∃ c : ℝ, 0 < c ∧ ∃ ε : ℝ, 0 < ε ∧
    ∀ᶠ x in (atTop : Filter ℝ), ε ≤ sidonWeight A c x

/-- The property the resolution node's "optimal function $f$" must have, stated for a general
weight `f`: "$\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}f(x)=0$ for all
infinite Sidon sets $A$".

⛔ OPTIMALITY IS NOT DEFINED, because the source does not say in which order `f` is to be
optimal (pointwise, up to constants, along a subsequence). This is a `def` describing a
property; nothing in this file claims any particular `f` has it, or that a best one exists. -/
def IsNullWeightForAllSidon (f : ℝ → ℝ) : Prop :=
  ∀ A : Set ℕ, A.Infinite → IsSidon A →
    liminf (fun x => (countUpTo A x : ℝ) / Real.sqrt x * f x) atTop = 0

/-! ### The one published bound the resolution node records -/

/-- **Erdős' bound** (resolution node; see [HaRo66]).

Source, verbatim: "Erdős proved (see for example \cite{HaRo66}) that if $A$ is an infinite
Sidon set then $\liminf_{x\to \infty} \frac{\lvert A\cap [1,x]\rvert}{x^{1/2}}(\log x)^{1/2}
\leq c$ for some constant $c>0$."

The constant is taken absolute (uniform in `A`, convention 8). This is a published theorem,
not one of the open questions; the proof is `sorry` here.

⛔ Note what this does NOT say: it bounds the liminf ABOVE by a constant. Question 1 asks
whether that liminf is `0`, and this bound neither answers it nor is answered by it. -/
theorem erdos_liminf_sqrt_log_le_const :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Set ℕ, A.Infinite → IsSidon A →
      liminf (sidonWeight A (1 / 2)) atTop ≤ C := by
  sorry

/-! ### Anti-vacuity controls (PROVED, no `sorry`, kernel-checked)

A `sorry`-carrying statement elaborates whether or not its definitions say anything. The
declarations below are fully proved, mention only this file's own definitions, and are cheap
machine-checked evidence that those definitions bite. -/

/-- **The load-bearing check on convention 3.** The counted set really is finite, for every
real cutoff `x` and every `A` — including infinite `A`. Without this, `Set.ncard` would be
silently returning its junk value `0` and both questions would be about nothing. -/
-- @category test
theorem finite_countSet (A : Set ℕ) (x : ℝ) : (countSet A x).Finite := by
  apply Set.Finite.subset (Set.finite_Icc 1 ⌊x⌋₊)
  rintro n ⟨-, h1, h2⟩
  exact ⟨h1, Nat.le_floor h2⟩

/-- The counting function is monotone in the cutoff, as any counting function must be. Uses
`finite_countSet`, so it also witnesses that the finiteness above is usable. -/
-- @category test
theorem countUpTo_mono (A : Set ℕ) {x y : ℝ} (h : x ≤ y) : countUpTo A x ≤ countUpTo A y := by
  refine Set.ncard_le_ncard ?_ (finite_countSet A y)
  rintro n ⟨hn, h1, h2⟩
  exact ⟨hn, h1, h2.trans h⟩

/-- **Convention 3 exhibited, lower end.** The interval is `[1, x]`, so below `1` nothing is
counted — in particular `0 ∈ A` is never counted. This is the degenerate region where
`sidonWeight` is junk (`Real.log x < 0`, `Real.sqrt x` possibly `0`); `liminf ... atTop`
ignores it, and this lemma is what makes that explicit rather than assumed. -/
-- @category test
theorem countUpTo_eq_zero_of_lt_one (A : Set ℕ) {x : ℝ} (hx : x < 1) : countUpTo A x = 0 := by
  have hempty : countSet A x = ∅ := by
    ext n
    simp only [countSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ h1 h2
    have h3 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  rw [countUpTo, hempty, Set.ncard_empty]

/-- **The two layers agree.** Question 1 is exactly the statement that the weight
`f(x) = (\log x)^{1/2}` is a null weight for all infinite Sidon sets, i.e. it is the
resolution node's `f`-formulation at the specific `f` the source names. Proved by
definitional unfolding, so it also checks that `sidonWeight` at `c = 1/2` really is the
expression `IsNullWeightForAllSidon` multiplies in. -/
-- @category test
theorem question1_iff_isNullWeight :
    Question1 ↔ IsNullWeightForAllSidon (fun x => Real.log x ^ (1 / 2 : ℝ)) :=
  Iff.rfl

/-- **The Sidon definition is not vacuous on the diagonal** (the degenerate-pair reading of
convention 1, carried over from `erdos-157.lean`): `a + a = c + d` with `a, c, d ∈ A` forces
`c = d`. If this failed, `IsSidon` would be the weaker non-B₂ condition. -/
-- @category test
theorem sidon_diagonal (A : Set ℕ) (h : IsSidon A) (a c d : ℕ) (ha : a ∈ A) (hc : c ∈ A)
    (hd : d ∈ A) (hsum : a + a = c + d) : c = d := by
  rcases h a ha a ha c hc d hd hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- A singleton is a Sidon set, so `IsSidon` is satisfiable and the questions are not
quantifying over an empty class of sets. (The INFINITE Sidon sets the questions are about are
harder to exhibit; this control only pins that the Sidon predicate itself is inhabited.) -/
-- @category test
theorem isSidon_singleton (m : ℕ) : IsSidon {m} := by
  rintro a rfl b rfl c rfl d rfl _
  exact Or.inl ⟨rfl, rfl⟩

end Erdos1191

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos1191.erdos_liminf_sqrt_log_le_const
#print axioms Erdos1191.finite_countSet
#print axioms Erdos1191.countUpTo_mono
#print axioms Erdos1191.countUpTo_eq_zero_of_lt_one
#print axioms Erdos1191.question1_iff_isNullWeight
#print axioms Erdos1191.sidon_diagonal
#print axioms Erdos1191.isSidon_singleton
