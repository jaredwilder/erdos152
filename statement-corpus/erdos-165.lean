/-
# Erdős problem 165 — an asymptotic formula for the off-diagonal Ramsey number `R(3,k)`

STATUS: **OPEN** (prize $250). This file states the QUESTION without committing to an answer,
and states, separately and each under its own name, the bounds the source records as KNOWN.

--------------------------------------------------------------------------------------------
SOURCE (frozen), `entry-graph-erdos-165.json`, node `n000-question` (kind: question), VERBATIM:

  "Give an asymptotic formula for $R(3,k)$."

SOURCE node `n001-resolution` (kind: resolution), VERBATIM:

  "It is known that there exists some constant $c>0$ such that for large $k$
   \[(c+o(1))\frac{k^2}{\log k}\leq R(3,k) \leq (1+o(1))\frac{k^2}{\log k}.\]
   The lower bound is due to Kim \cite{Ki95}, the upper bound is due to Shearer \cite{Sh83},
   improving an earlier bound of Ajtai, Komlós, and Szemerédi \cite{AKS80}. The value of $c$
   in the lower bound has seen a number of improvements. Kim's original proof gave
   $c\geq 1/162$. The bound $c\geq 1/4$ was proved independently by Bohman and Keevash
   \cite{BoKe21} and Pontiveros, Griffiths and Morris \cite{PGM20}. The latter collection of
   authors conjecture that this lower bound is the true order of magnitude. This was, however,
   improved by Campos, Jenssen, Michelen, and Sahasrabudhe \cite{CJMS25} to $c\geq 1/3$, and
   further by Hefty, Horn, King, and Pfender \cite{HHKP25} to $c\geq 1/2$. Both of these papers
   conjecture that $c=1/2$ is the correct asymptotic. See also [544] , and [986] for the
   general case. See [1013] for a related function."

--------------------------------------------------------------------------------------------
WHAT IS ASKED VERSUS WHAT IS KNOWN — KEPT APART, DELIBERATELY.

  * `Erdos165.Question`      — the open question, as a `Prop`. It does NOT name a constant.
  * `kim_shearer_bounds`     — the matching-order sandwich the source calls "known".
  * `shearer_upper_bound`, `kim_lower_bound`, `bohman_keevash_pgm_lower_bound`,
    `campos_jenssen_michelen_sahasrabudhe_lower_bound`, `hefty_horn_king_pfender_lower_bound`
                             — the individual known bounds, one theorem each.
  * `Conjecture_c_eq_half`, `Conjecture_pgm_quarter_is_truth`
                             — recorded as `def ... : Prop`. They are CONJECTURES in the
                               source and are therefore NOT stated as theorems here.

⛔ NO EXACT ASYMPTOTIC CONSTANT IS ASSERTED ANYWHERE IN THIS FILE. The source says the constant
`c` is not known; the best recorded lower bound is `c ≥ 1/2` and the best recorded upper bound
is `1`. Writing `R(3,k) ~ (1/2) k²/log k` as a theorem — even a sorried one — would be a
fabricated result, not a formalization. The gap between `1/2` and `1` IS the open problem.

--------------------------------------------------------------------------------------------
MATHLIB GAP (measured, 2026-08-28).

Mathlib has **no Ramsey number**. `grep -ri ramsey Mathlib/Combinatorics/` returns only prose
mentions inside `Hindman.lean` and `HalesJewett.lean` ("a result in Ramsey theory"); there is no
`SimpleGraph.ramseyNumber`, no `Nat.ramsey`, nothing in `Mathlib/Combinatorics/SimpleGraph/`.
So `R` is defined here, from the colouring condition, on top of Mathlib's own clique API
(`SimpleGraph.CliqueFree`, `SimpleGraph.IsNClique`). Everything else is Mathlib's.

--------------------------------------------------------------------------------------------
CONVENTIONS THE SOURCE LEAVES UNSTATED — every one named, with the reading taken.

(1) OFF-DIAGONAL, NOT DIAGONAL. `R(3,k)` is the two-parameter Ramsey number with the first
    parameter pinned at `3`; it is not the diagonal `R(k,k)`. The asymptotics are completely
    different (`R(k,k)` is exponential in `k`), so this is the single most consequential
    convention in the file. The variable that goes to infinity is the SECOND argument.

(2) "monochromatic copy" — read in the standard graph form. A red/blue colouring of the edges
    of the complete graph on `n` vertices is encoded as a single `G : SimpleGraph (Fin n)`
    (red = adjacency in `G`), with blue = adjacency in the complement `Gᶜ`. "A monochromatic
    `K₃` in red" is then `¬ G.CliqueFree 3`, and "a monochromatic `K_k` in blue" is
    `¬ Gᶜ.CliqueFree k`. Equivalently, and identically: `G` contains a triangle or an
    INDEPENDENT SET of size `k`. On a simple graph, `Gᶜ`-cliques ARE `G`-independent sets, so
    the two phrasings of the problem coincide; no choice is being made between them.

(3) VERTEX SET = `Fin n`. Canonical, and the choice is immaterial: the condition is invariant
    under graph isomorphism, and any `n`-element type is equivalent to `Fin n`. Stating it over
    `Fin n` avoids quantifying over a universe of types.

(4) `R s t` is the LEAST `n` for which the condition holds, taken as `sInf` over `ℕ`. If the
    defining set were empty, Mathlib's `Nat.sInf` returns `0`; that junk value is never used,
    since every statement below is either proved from an explicit membership or is asymptotic.
    Ramsey's theorem (which would show the set is always nonempty) is NOT in Mathlib either,
    so `R_mono_right` carries a nonemptiness hypothesis rather than assuming it.

(5) `\log` = NATURAL logarithm, `Real.log`. (In this literature `log` is always natural; the
    base only rescales the constant `c`, which is exactly the quantity in question, so getting
    it wrong would change the problem.) `Real.log 0 = Real.log 1 = 0`, so `k²/log k` is Lean
    junk (`x/0 = 0`) at `k ∈ {0,1}`. Every statement below is `∀ᶠ k in atTop` or a limit as
    `k → ∞`, so no statement ever reads those two values.

(6) `(c + o(1)) g(k) ≤ R(3,k) ≤ (1 + o(1)) g(k)` is rendered in the standard eventual-ε form:
    for every `ε > 0`, the inequality with `c - ε` (resp. `1 + ε`) holds for all large `k`.
    This is the exact meaning of the printed `o(1)`, not a weakening of it.

(7) "Give an asymptotic formula" is rendered as: does `R(3,k) · log k / k²` CONVERGE? An
    asymptotic formula of the shape the resolution node establishes is precisely a value for
    that limit. The `Prop` asserts the existence of SOME real limit `c` and names no number.
    HONESTY NOTE: this is one reading of a deliberately informal request. A formula could in
    principle have a different shape (e.g. secondary terms), so `Question` is a *sufficient*
    formalization of "there is an asymptotic formula of the established shape", and its
    failure would itself be a major result. The reading is stated here rather than hidden.

(8) `k` ranges over ℕ and `k → ∞` is `Filter.atTop` on ℕ.
-/

-- @category research open
-- @AMS 5
-- Category vocabulary and AMS tagging adopted from the
-- formal-conjectures corpus (509 files, measured 2026-08-28). Written as a comment
-- rather than the corpus attribute form, so this artifact still elaborates
-- standalone, outside their project.




import Mathlib
open Filter Topology

namespace Erdos165

/-! ### The definition: `R(s,t)` from the colouring condition -/

/-- `IsRamseyBound s t n` : every red/blue colouring of the edges of the complete graph on
`n` vertices contains a red `K_s` or a blue `K_t`.

The colouring is encoded as a graph `G : SimpleGraph (Fin n)` (red = `G`, blue = `Gᶜ`), so a
red `K_s` is `¬ G.CliqueFree s` and a blue `K_t` is `¬ Gᶜ.CliqueFree t`. Since `Gᶜ`-cliques are
exactly `G`-independent sets, this also reads: every graph on `n` vertices has an `s`-clique or
an independent set of size `t`. -/
def IsRamseyBound (s t n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t

/-- The set of orders `n` that force a red `K_s` or a blue `K_t`. -/
def RamseySet (s t : ℕ) : Set ℕ := {n | IsRamseyBound s t n}

/-- `R s t` : the (off-diagonal) Ramsey number, the least `n` forcing a red `K_s` or a blue
`K_t`. ⛔ Mathlib has no Ramsey number; this is defined here (see the MATHLIB GAP note in the
file header). -/
noncomputable def R (s t : ℕ) : ℕ := sInf (RamseySet s t)

/-! ### PROVED controls — no `sorry`. These exist so that the definitions above are
falsifiable by compilation rather than merely elaborating. -/

/-- **Control (proved).** One vertex already forces a blue `K₁`, for any `s`. -/
theorem isRamseyBound_one_right (s : ℕ) : IsRamseyBound s 1 1 := by
  intro G
  refine Or.inr ?_
  rw [SimpleGraph.cliqueFree_one, not_isEmpty_iff]
  exact ⟨0⟩

/-- **Control (proved).** Zero vertices force nothing, as soon as both parameters are positive:
the empty graph has neither an `s`-clique nor a blue `t`-clique. -/
theorem not_isRamseyBound_zero {s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    ¬ IsRamseyBound s t 0 := by
  intro h
  rcases h ⊥ with h1 | h1
  · exact h1 (SimpleGraph.cliqueFree_of_card_lt (by simpa using hs))
  · exact h1 (SimpleGraph.cliqueFree_of_card_lt (by simpa using ht))

/-- **Control (proved).** `R(3,1) = 1`. The first value of the very function this problem is
about, computed from the definition. -/
theorem R_three_one : R 3 1 = 1 := by
  have h1 : (1 : ℕ) ∈ RamseySet 3 1 := isRamseyBound_one_right 3
  have hle : R 3 1 ≤ 1 := Nat.sInf_le h1
  have hmem : R 3 1 ∈ RamseySet 3 1 := Nat.sInf_mem ⟨1, h1⟩
  have hne : R 3 1 ≠ 0 := by
    intro h0
    rw [h0] at hmem
    exact not_isRamseyBound_zero (by norm_num) (by norm_num) hmem
  omega

/-- **Control (proved).** Monotonicity of the forcing condition in the second parameter: a
blue `K_t` contains a blue `K_{t'}` whenever `t' ≤ t`. -/
theorem isRamseyBound_mono_right {s t t' n : ℕ} (h : t' ≤ t) (hb : IsRamseyBound s t n) :
    IsRamseyBound s t' n := by
  intro G
  rcases hb G with h1 | h1
  · exact Or.inl h1
  · exact Or.inr fun hf => h1 (hf.mono h)

/-- **Control (proved).** `R(s, ·)` is monotone. The nonemptiness hypothesis stands in for
Ramsey's theorem, which Mathlib does not have (see convention (4)). -/
theorem R_mono_right {s t t' : ℕ} (h : t' ≤ t) (hne : (RamseySet s t).Nonempty) :
    R s t' ≤ R s t :=
  Nat.sInf_le (isRamseyBound_mono_right h (Nat.sInf_mem hne))

/-! ### The scale appearing in the problem -/

/-- The scale `k² / log k` against which `R(3,k)` is measured. `Real.log` is the NATURAL
logarithm (convention (5)); the value at `k ∈ {0,1}` is Lean junk and is never read, since
every statement below is eventual in `k`. -/
noncomputable def scale (k : ℕ) : ℝ := (k : ℝ) ^ 2 / Real.log k

/-! ### ⭐ THE QUESTION — stated WITHOUT committing to a constant -/

/-- **Erdős problem 165, the question.**

  *"Give an asymptotic formula for $R(3,k)$."*

Rendered (convention (7)) as: does `R(3,k) · log k / k²` converge? An asymptotic formula of the
shape established by Kim and Shearer is exactly a value of this limit.

⛔ THIS `Prop` NAMES NO CONSTANT. It asserts only that SOME real limit exists. Whether it holds,
and what `c` is if it does, is the open problem. -/
def Question : Prop :=
  ∃ c : ℝ, Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 c)

/-! ### KNOWN — each bound the source records, as its own theorem. Proofs are `sorry`:
these are cited literature results, not results of this file. -/

/-- **Shearer (1983)**, improving Ajtai–Komlós–Szemerédi (1980). The upper bound
`R(3,k) ≤ (1 + o(1)) k²/log k`. -/
theorem shearer_upper_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (R 3 k : ℝ) ≤ (1 + ε) * scale k := by
  sorry

/-- **Kim (1995).** There is a constant `c > 0` with `R(3,k) ≥ (c + o(1)) k²/log k`.
The theorem asserts only that SUCH A CONSTANT EXISTS; the numerical improvements to `c` are
stated separately below. -/
theorem kim_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (c - ε) * scale k ≤ (R 3 k : ℝ) := by
  sorry

/-- **Kim's original constant.** `c ≥ 1/162`. -/
theorem kim_lower_bound_162 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ((1 : ℝ) / 162 - ε) * scale k ≤ (R 3 k : ℝ) := by
  sorry

/-- **Bohman–Keevash (2021)** and, independently, **Fiz Pontiveros–Griffiths–Morris (2020)**.
`c ≥ 1/4`. -/
theorem bohman_keevash_pgm_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ((1 : ℝ) / 4 - ε) * scale k ≤ (R 3 k : ℝ) := by
  sorry

/-- **Campos–Jenssen–Michelen–Sahasrabudhe (2025).** `c ≥ 1/3`. -/
theorem campos_jenssen_michelen_sahasrabudhe_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ((1 : ℝ) / 3 - ε) * scale k ≤ (R 3 k : ℝ) := by
  sorry

/-- **Hefty–Horn–King–Pfender (2025).** `c ≥ 1/2` — the best lower constant the source
records. -/
theorem hefty_horn_king_pfender_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ((1 : ℝ) / 2 - ε) * scale k ≤ (R 3 k : ℝ) := by
  sorry

/-- **The sandwich the source calls "known"**, exactly as printed:
`(c + o(1)) k²/log k ≤ R(3,k) ≤ (1 + o(1)) k²/log k` for some `c > 0`. -/
theorem kim_shearer_bounds :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop,
        (c - ε) * scale k ≤ (R 3 k : ℝ) ∧ (R 3 k : ℝ) ≤ (1 + ε) * scale k := by
  sorry

/-- **Order of magnitude (Kim's title).** `R(3,k) = Θ(k²/log k)`: the two bounds above have the
same shape, so the ratio is bounded above and below by positive constants for large `k`. This
is strictly weaker than `Question`, and is what is actually settled. -/
theorem order_of_magnitude :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ᶠ k : ℕ in atTop, a * scale k ≤ (R 3 k : ℝ) ∧ (R 3 k : ℝ) ≤ b * scale k := by
  sorry

/-- **What the known bounds would say about the answer, IF the limit exists.** Conditional on
`Question`, the constant is pinned to `[1/2, 1]` by `hefty_horn_king_pfender_lower_bound` and
`shearer_upper_bound`. This asserts nothing about whether the limit exists, and does not name
the constant — the interval `[1/2, 1]` is the width of the open problem. -/
theorem question_constant_mem_Icc :
    Question →
      ∃ c : ℝ, (1 : ℝ) / 2 ≤ c ∧ c ≤ 1 ∧
        Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 c) := by
  sorry

/-! ### CONJECTURES recorded by the source. ⛔ These are `def ... : Prop`, NOT theorems: the
source presents them as conjectures, and stating a conjecture as a (sorried) theorem is how a
guess becomes indistinguishable from a result. -/

/-- **Conjecture (Fiz Pontiveros–Griffiths–Morris).** *"The latter collection of authors
conjecture that this lower bound is the true order of magnitude"* — i.e. `c = 1/4` is the
truth. Superseded by the later `c ≥ 1/3` and `c ≥ 1/2` lower bounds, and recorded here only
because the source records it. -/
def Conjecture_pgm_quarter_is_truth : Prop :=
  Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 ((1 : ℝ) / 4))

/-- **Conjecture (Campos–Jenssen–Michelen–Sahasrabudhe; Hefty–Horn–King–Pfender).**
*"Both of these papers conjecture that $c=1/2$ is the correct asymptotic."* -/
def Conjecture_c_eq_half : Prop :=
  Tendsto (fun k : ℕ => (R 3 k : ℝ) * Real.log k / (k : ℝ) ^ 2) atTop (𝓝 ((1 : ℝ) / 2))

/-- Either conjecture, if true, answers `Question`. Stated as an implication so that the
relationship is machine-readable without either conjecture being asserted. -/
theorem conjecture_c_eq_half_implies_question : Conjecture_c_eq_half → Question :=
  fun h => ⟨(1 : ℝ) / 2, h⟩

end Erdos165

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos165.isRamseyBound_one_right
#print axioms Erdos165.not_isRamseyBound_zero
#print axioms Erdos165.R_three_one
#print axioms Erdos165.isRamseyBound_mono_right
#print axioms Erdos165.R_mono_right
#print axioms Erdos165.shearer_upper_bound
#print axioms Erdos165.kim_lower_bound
#print axioms Erdos165.kim_lower_bound_162
#print axioms Erdos165.bohman_keevash_pgm_lower_bound
#print axioms Erdos165.campos_jenssen_michelen_sahasrabudhe_lower_bound
#print axioms Erdos165.hefty_horn_king_pfender_lower_bound
#print axioms Erdos165.kim_shearer_bounds
#print axioms Erdos165.order_of_magnitude
#print axioms Erdos165.question_constant_mem_Icc
#print axioms Erdos165.conjecture_c_eq_half_implies_question
