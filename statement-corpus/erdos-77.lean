/-
# Erdős problem 77 — the growth rate of the diagonal Ramsey numbers (OPEN)

SOURCE (frozen), `entry-graph-erdos-77.json`, node `n000-question` (kind: question),
quoted verbatim:

  "If $R(k)$ is the Ramsey number for $K_k$, the minimal $n$ such that every $2$-colouring of
   the edges of $K_n$ contains a monochromatic copy of $K_k$, then find the value of
   \[\lim_{k\to \infty}R(k)^{1/k}.\]"

SOURCE node `n001-resolution` (kind: resolution), the part that records what is KNOWN:

  "Erd\H{o}s offered \$100 for just a proof of the existence of this constant, without
   determining its value. He also offered \$1000 for a proof that the limit does not exist, but
   says 'this is really a joke as [it] certainly exists'. (In \cite{Er88} he raises this prize
   to \$10000). Erd\H{o}s proved
   \[\sqrt{2}\leq \liminf_{k\to \infty}R(k)^{1/k}\leq \limsup_{k\to \infty}R(k)^{1/k}\leq 4.\]
   The upper bound has been improved to $4-\tfrac{1}{128}$ by Campos, Griffiths, Morris, and
   Sahasrabudhe \cite{CGMS23}. This was improved to $3.7992\cdots$ by Gupta, Ndiaye, Norin, and
   Wei \cite{GNNW24}. A shorter and simpler proof of an upper bound of the strength $4-c$ for
   some constant $c>0$ (and a generalisation to the case of more than two colours) was given by
   Balister, Bollob\'{a}s, Campos, Griffiths, Hurley, Morris, Sahasrabudhe, and Tiba
   \cite{BBCGHMST24}. In \cite{Er93} Erd\H{o}s writes 'I have no idea what the value of
   $\lim R(k)^{1/k}$ should be, perhaps it is $2$ but we have no real evidence for this.'"

STATUS: **OPEN.** This file therefore states a QUESTION and does not answer it.

⛔ NOTHING IN THIS FILE ASSERTS A VALUE FOR THE LIMIT, AND NOTHING ASSERTS THAT THE LIMIT
EXISTS. Erdős's own guess of `2` appears in the source and is deliberately NOT formalized as a
theorem: it is recorded there as a guess with, in his words, "no real evidence". The existence
of the limit is itself the $100 (later $10000) prize problem, so `LimitExists` below is a `def`
of a proposition — never a `theorem`.

--------------------------------------------------------------------------------------------
WHAT MATHLIB HAS, AND WHY NOTHING IS REUSED

Searched the only built Mathlib on this host (`/root/erdosfire-bench/proofs`,
toolchain v4.31.0-rc1) for Ramsey material:

  * `grep -ril ramsey Mathlib/` matches five files — `Combinatorics/Hindman.lean`,
    `Combinatorics/HalesJewett.lean`, and three `RingTheory/*Algebra/Basic.lean` — and in every
    one the word occurs only in prose/attribution. There is **no `ramseyNumber`, no
    `SimpleGraph.Ramsey`, and no Ramsey-number namespace in Mathlib.** So `R` is defined here
    from the colouring condition, as the source states it, rather than imported.
  * `Mathlib.Combinatorics.Pigeonhole` proves pigeonhole principles only; it carries no Ramsey
    statement and is not on the path to one for this file.
  * `Mathlib.Combinatorics.SimpleGraph.Clique` DOES have `SimpleGraph.IsNClique` and
    `SimpleGraph.CliqueFree`, which would support the equivalent graph-theoretic reading
    "`R(k)` = least `n` such that every `G : SimpleGraph (Fin n)` has a `k`-clique in `G` or in
    `Gᶜ`". That reading is not taken, because the source speaks of a 2-colouring of edges and
    the colouring form is the literal one; the two are equivalent (red = adjacency) but the
    equivalence is a lemma nobody here has proved, so it is NOT claimed.

Mathlib IS used for everything else: `Sym2` for unordered edges, `Nat.sInf` for the minimum,
`Real.rpow` for `R(k)^{1/k}`, and `Filter.limsup` / `Filter.liminf` for the two bounds.

--------------------------------------------------------------------------------------------
CONVENTIONS THE SOURCE LEAVES UNSTATED — every one named, with the reading taken.

(1) `R(k)` is the DIAGONAL Ramsey number `R(k,k)`. The source writes "the Ramsey number for
    $K_k$" with a single parameter and asks for a monochromatic `K_k` in EITHER colour, so both
    colour classes carry the same clique size. Off-diagonal numbers `R(s,t)` are a different
    problem (see the source's own cross-reference to [1029]) and are not formalized here.

(2) VERTEX SET. "the edges of $K_n$" is read as the edges of the complete graph on `Fin n`.
    Any `n`-element type gives the same value; `Fin n` is chosen so that `n` is literally the
    cardinality and `Fintype.card_fin` is available.

(3) EDGES AS `Sym2`. A colouring is `Sym2 (Fin n) → Bool`. Using `Sym2` means the colouring is
    symmetric BY CONSTRUCTION — there is no way to colour `xy` and `yx` differently — so no
    symmetry hypothesis has to be carried, and none can be forgotten. The domain `Sym2` also
    contains the diagonal elements `s(x,x)`, which are not edges of `K_n`; they are harmless
    because every condition below is guarded by `x ≠ y`, so the values a colouring takes on the
    diagonal are never read. `Bool` is "2-colouring": exactly two colours, and decidable
    equality of colours for free.

(4) "CONTAINS A MONOCHROMATIC COPY OF $K_k$" is read as: there is a set of `k` vertices and a
    SINGLE colour `c` such that every pair of DISTINCT vertices of that set has colour `c`.
    The quantifier order matters and is stated explicitly (`∃ c, ∀ x y`): "each pair is
    monochromatic" — `∀ x y, ∃ c` — would be vacuous, since every single edge has some colour.
    A "copy of `K_k`" is a `k`-SUBSET, not an injection from `Fin k`; the two are equivalent
    and the subset form is what `Finset.card = k` says.

(5) "THE MINIMAL $n$" is `Nat.sInf` of the set of `n` that work. Two consequences are named
    rather than hidden. (a) If that set were EMPTY, `Nat.sInf` returns `0`, so `R k = 0` would
    mean "no such `n` exists", not "zero works". Ramsey's theorem says the set is never empty,
    but that theorem is NOT proved in this file and is not in Mathlib, so every statement
    below that needs nonemptiness takes it as an explicit hypothesis (`le_R`). (b) The set is
    upward closed in `n` (a colouring of `K_n` restricts from one of `K_{n+1}`), which is what
    makes "minimal element" and "infimum" agree; that monotonicity is standard, is not needed
    for any statement here, and is not claimed.

(6) `R(k)^{1/k}` is `Real.rpow` applied to the cast `(R k : ℝ)`: real base, real exponent
    `1 / k`. At `k = 0` this evaluates to `(0 : ℝ) ^ (0 : ℝ) = 1` because `1 / 0 = 0` in ℝ —
    an artefact of totality that no statement here depends on, since every claim is about the
    filter `atTop`.

(7) `k → ∞` ranges over the NATURAL NUMBERS (`Filter.atTop` on ℕ).

(8) `liminf` and `limsup` are `Filter.liminf` / `Filter.limsup` valued in ℝ, which is a
    conditionally complete lattice. Erdős's chain is stated as ONE conjunction, exactly as the
    source prints it, including the middle inequality `liminf ≤ limsup` (which in a
    conditionally complete lattice is a boundedness statement, not a triviality).

(9) "$3.7992\cdots$" is a TRUNCATED DECIMAL, not the exact constant of Gupta–Ndiaye–Norin–Wei.
    It is formalized as "there is a constant `c` with `3.7992 ≤ c ≤ 3.7993` bounding the
    limsup", which is what a decimal printed to four places licenses and no more. Writing
    `limsup ≤ 3.7992` would claim a bound the source does not state.

(10) THE PRIZES are recorded in prose only. "$100 for a proof that the constant exists" is the
     proposition `LimitExists`; "$1000 (later $10000) for a proof that the limit does not
     exist" is its negation. Neither is asserted.
-/

-- @category research open
-- @AMS 5
-- Category vocabulary and AMS tagging adopted from the formal-conjectures corpus
-- (509 files, measured 2026-08-28). Written as a comment rather than the corpus
-- attribute form, so this artifact still elaborates standalone, outside their project.







import Mathlib
open Filter Topology

namespace Erdos77

/-! ### The Ramsey number `R(k)`, defined from the colouring condition -/

/-- A `2`-colouring of the edges of the complete graph `K_n` on the vertex set `Fin n`.
Edges are unordered pairs (`Sym2`), so a colouring is symmetric by construction; its values on
the diagonal `s(x,x)` are never read (every condition below is guarded by `x ≠ y`). -/
abbrev Colouring (n : ℕ) := Sym2 (Fin n) → Bool

/-- `s` is a monochromatic copy of `K_k` for the colouring `C`: a set of `k` vertices together
with a SINGLE colour `c` received by every pair of distinct vertices of `s`. -/
def IsMonoClique {n : ℕ} (C : Colouring n) (k : ℕ) (s : Finset (Fin n)) : Prop :=
  s.card = k ∧ ∃ c : Bool, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C (Sym2.mk x y) = c

/-- `Arrows n k` : *every* `2`-colouring of the edges of `K_n` contains a monochromatic copy of
`K_k`. This is the property whose least witness `n` the source calls `R(k)`. -/
def Arrows (n k : ℕ) : Prop := ∀ C : Colouring n, ∃ s : Finset (Fin n), IsMonoClique C k s

/-- `R k` : "the minimal `n` such that every `2`-colouring of the edges of `K_n` contains a
monochromatic copy of `K_k`", i.e. the diagonal Ramsey number `R(k,k)`.

⛔ Convention (5): this is `Nat.sInf`, so `R k = 0` also encodes "no such `n` exists". That case
is ruled out for every `k` by Ramsey's theorem, which is not proved here and is not in Mathlib,
so `le_R` below takes nonemptiness as a hypothesis rather than assuming it. -/
noncomputable def R (k : ℕ) : ℕ := sInf {n : ℕ | Arrows n k}

/-! ### Proved controls (no `sorry`) — evidence that the definitions above bite -/

/-- Anti-vacuity control. The empty set is a monochromatic copy of `K_0`, so `K_0` is found in
every colouring of every `K_n`. -/
@[simp]
theorem arrows_zero (n : ℕ) : Arrows n 0 := by
  intro C
  exact ⟨∅, by simp, true, by simp⟩

/-- Degenerate value: `R 0 = 0`. -/
theorem R_zero : R 0 = 0 := by
  have h : (0 : ℕ) ∈ {n : ℕ | Arrows n 0} := arrows_zero 0
  exact Nat.sInf_eq_zero.mpr (Or.inl h)

/-- Control on the DEFINITION, not on a colouring: a monochromatic `K_k` inside `K_n` is a
`k`-element subset of an `n`-element vertex set, so `Arrows n k` forces `k ≤ n`. Proved by
feeding the definition the constant colouring. -/
theorem card_le_of_arrows {n k : ℕ} (h : Arrows n k) : k ≤ n := by
  obtain ⟨s, hcard, -⟩ := h (fun _ => true)
  have hle : s.card ≤ Fintype.card (Fin n) := Finset.card_le_univ s
  simpa [hcard] using hle

/-- Anti-vacuity control at `k = 1`: a single vertex is a monochromatic `K_1`, vacuously. -/
theorem arrows_one : Arrows 1 1 := by
  intro C
  refine ⟨{0}, by simp, true, ?_⟩
  intro x hx y hy hxy
  simp only [Finset.mem_singleton] at hx hy
  exact absurd (hx.trans hy.symm) hxy

/-- Computed small case: `R 1 = 1`. Uses both directions — `1` works, and `0` does not, the
latter via `card_le_of_arrows`. -/
theorem R_one : R 1 = 1 := by
  have h1 : (1 : ℕ) ∈ {n : ℕ | Arrows n 1} := arrows_one
  refine le_antisymm (Nat.sInf_le h1) ?_
  have hne : R 1 ≠ 0 := by
    intro h
    rcases Nat.sInf_eq_zero.mp h with h0 | he
    · have := card_le_of_arrows h0
      omega
    · rw [he] at h1
      simp at h1
  omega

/-- `k ≤ R k`, given that some `n` works at all. The hypothesis is exactly the content of
Ramsey's theorem for `k`, which this file does not prove (convention (5)). -/
theorem le_R {k : ℕ} (h : {n : ℕ | Arrows n k}.Nonempty) : k ≤ R k :=
  card_le_of_arrows (Nat.sInf_mem h)

/-! ### The quantity whose limit is asked for -/

/-- `growth k = R(k)^{1/k}`, real exponentiation of the cast Ramsey number
(conventions (6), (7)). -/
noncomputable def growth (k : ℕ) : ℝ := (R k : ℝ) ^ ((1 : ℝ) / (k : ℝ))

/-! ### THE QUESTION — stated without committing to an answer -/

/-- **Erdős problem 77.** `Question L` says: the limit `lim_{k→∞} R(k)^{1/k}` exists and equals
`L`.

  "If $R(k)$ is the Ramsey number for $K_k$, the minimal $n$ such that every $2$-colouring of
   the edges of $K_n$ contains a monochromatic copy of $K_k$, then find the value of
   \[\lim_{k\to \infty}R(k)^{1/k}.\]"

⛔ `L` is a PARAMETER. No declaration in this file instantiates it. The problem is OPEN: no
value of `L` is known, and it is not even known that any `L` works. -/
def Question (L : ℝ) : Prop := Tendsto growth atTop (𝓝 L)

/-- The weaker `$100` (later `$10000`) question recorded in the source: does the constant exist
at all, whatever its value? Its negation is the `$1000` question ("a proof that the limit does
not exist"). Stated as a `def`; neither it nor its negation is asserted anywhere below. -/
def LimitExists : Prop := ∃ L : ℝ, Question L

/-! ### What the SOURCE records as known.

These are `sorry`-carrying STATEMENTS of published results, included because the source's
resolution node records them. They constrain any answer to `Question` without determining one:
together they place the limit — if it exists — in `[√2, 3.7993]`. -/

/-- **Erdős.** `√2 ≤ liminf R(k)^{1/k} ≤ limsup R(k)^{1/k} ≤ 4`, stated as the source prints
it, as a single chain (convention (8)). -/
-- @category research solved
theorem erdos_liminf_limsup_bounds :
    Real.sqrt 2 ≤ liminf growth atTop ∧
      liminf growth atTop ≤ limsup growth atTop ∧
        limsup growth atTop ≤ 4 := by
  sorry

/-- **Campos, Griffiths, Morris, Sahasrabudhe (2023)** \cite{CGMS23}: the upper bound `4` is
improved to `4 - 1/128`. -/
-- @category research solved
theorem campos_griffiths_morris_sahasrabudhe_bound :
    limsup growth atTop ≤ 4 - 1 / 128 := by
  sorry

/-- **Gupta, Ndiaye, Norin, Wei (2024)** \cite{GNNW24}: the upper bound is improved to
`$3.7992\cdots$`. The trailing dots are a truncation, so the claim formalized is the one the
printed decimal licenses (convention (9)): some constant in `[3.7992, 3.7993]` bounds the
limsup. -/
-- @category research solved
theorem gupta_ndiaye_norin_wei_bound :
    ∃ c : ℝ, 3.7992 ≤ c ∧ c ≤ 3.7993 ∧ limsup growth atTop ≤ c := by
  sorry

/-- **Balister, Bollobás, Campos, Griffiths, Hurley, Morris, Sahasrabudhe, Tiba (2024)**
\cite{BBCGHMST24}: a shorter and simpler proof of an upper bound of the strength `4 - c` for
some constant `c > 0`. (The source also records a generalisation to more than two colours,
which is a different statement and is not formalized here.) -/
-- @category research solved
theorem balister_et_al_bound :
    ∃ c : ℝ, 0 < c ∧ limsup growth atTop ≤ 4 - c := by
  sorry

end Erdos77

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos77.arrows_zero
#print axioms Erdos77.R_zero
#print axioms Erdos77.card_le_of_arrows
#print axioms Erdos77.arrows_one
#print axioms Erdos77.R_one
#print axioms Erdos77.le_R
#print axioms Erdos77.erdos_liminf_limsup_bounds
#print axioms Erdos77.campos_griffiths_morris_sahasrabudhe_bound
#print axioms Erdos77.gupta_ndiaye_norin_wei_bound
#print axioms Erdos77.balister_et_al_bound
