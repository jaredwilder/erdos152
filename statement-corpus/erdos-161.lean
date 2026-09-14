/-
# Erdős problem #161 — jumps of $F^{(t)}(n,\alpha)$  (**OPEN**, \$500 prize)

## The question (verbatim from the frozen source, node `n000-question`)

> Let $\alpha\in[0,1/2)$ and $n,t\geq 1$. Let $F^{(t)}(n,\alpha)$ be the smallest $m$ such that we
> can $2$-colour the edges of the complete $t$-uniform hypergraph on $n$ vertices such that if
> $X\subseteq [n]$ with $\lvert X\rvert \geq m$ then there are at least $\alpha
> \binom{\lvert X\rvert}{t}$ many $t$-subsets of $X$ of each colour. For fixed $n,t$ as we change
> $\alpha$ from $0$ to $1/2$ does $F^{(t)}(n,\alpha)$ increase continuously or are there jumps?
> Only one jump?

## The resolution node (verbatim, node `n001-resolution`)

> For $\alpha=0$ this is the usual Ramsey function. A conjecture of Erd\H{o}s, Hajnal, and Rado
> (see [562]) implies that
> \[ F^{(t)}(n,0)\asymp \log_{t-1} n\]
> and results of Erd\H{o}s and Spencer imply that
> \[F^{(t)}(n,\alpha) \gg_\alpha (\log n)^{\frac{1}{t-1}}\]
> for all $\alpha>0$, and a similar upper bound holds for $\alpha$ close to $1/2$. Erd\H{o}s said
> in \cite{Er90b}: 'If I can hazard a guess completely unsupported by evidence, I am afraid that
> the jump occurs all in one step at $0$. It would be much more interesting if my conjecture would
> be wrong and perhaps there is some hope for this for $t>3$. I know nothing and offer \$500 to
> anybody who can clear up this mystery.' Conlon, Fox, and Sudakov \cite{CFS11} have proved that,
> for any fixed $\alpha>0$,
> \[F^{(3)}(n,\alpha) \ll_\alpha \sqrt{\log n}.\]
> Coupled with the lower bound above, this implies that there is only one jump for fixed $\alpha$
> when $t=3$, at $\alpha=0$. For all $\alpha>0$ it is known that
> \[F^{(t)}(n,\alpha)\gg_t (\log n)^{c_\alpha}.\]
> See also [563] for more on the case $t=2$.

## What is formalized here — and what is deliberately NOT

**This problem is OPEN.**  `Erdos161.Question`, `Erdos161.NoJumps`, `Erdos161.ExactlyOneJump` and
`Erdos161.ErdosGuess` are all `def ... : Prop`, never theorems.  There is no
`erdos_161_resolution`, and nothing in this file asserts whether the jumps exist, how many there
are, or where they are — except in the one place where the LITERAL reading of the source's own
definition forces a trivial answer, and that place is proved and flagged rather than hidden (see
the next section, which is the main finding of this artifact).

⛔ Erdős's own guess ("the jump occurs all in one step at $0$") is `ErdosGuess`, a `def : Prop`.
The source calls it "a guess completely unsupported by evidence"; it is not a theorem here.

## ⛔ THE LITERAL READING OF $\alpha=0$ IS DEGENERATE, AND IT TRIVIALISES ERDŐS'S GUESS

Transcribed literally, the defining condition at $\alpha=0$ reads *"there are at least
$0\cdot\binom{|X|}{t}$ many $t$-subsets of $X$ of each colour"* — a condition satisfied by every
colouring and every $X$.  So the literal $F^{(t)}(n,0)$ is $0$: `F_zero` (PROVED).

That single fact wrecks three things at once, each of them proved below rather than asserted:

* `F_zero` : `F t n 0 = 0`.
* `t_lt_F` : for every `α > 0` and `t ≤ n`, `t < F t n α`.  (A set `X` of exactly `t` vertices has
  exactly one `t`-subset, which has one colour, so the other colour's count is `0`, and `0 ≥ α`
  fails.)  Hence `F t n α ≥ 1 > 0 = F t n 0`.
* `literal_jump_at_zero` : `F t n 0 < F t n α` for every `α > 0` and `t ≤ n` — the function
  already "jumps at 0" for every fixed `n`, for reasons that have nothing to do with Ramsey theory.
* `not_sameOrder_F_zero` : the same collapse survives the asymptotic reading — `n ↦ F t n 0` is
  identically `0`, so it is not `≍` to `n ↦ F t n α` for any `α > 0`, whatever those functions do.

⛔ **The source's own resolution node is therefore inconsistent with the literal reading**, and
says so itself: it records $F^{(t)}(n,0)\asymp\log_{t-1}n$, which the constant zero function is
not.  Following the discipline that a source's printed claim may be false as literally written,
the reading is FIXED BY THE SOURCE'S OWN SENTENCE — *"For $\alpha=0$ this is the usual Ramsey
function"* — and both objects are carried explicitly:

| object | what it is | status here |
|---|---|---|
| `F t n α` | the LITERAL transcription, for all `α ∈ [0,1/2)` | defined; its `α = 0` degeneracy PROVED |
| `FRamsey t n` | *"the usual Ramsey function"*: the least `m` admitting a colouring in which no `X` with `|X| ≥ m` is monochromatic | defined |
| `G t n α` | the source's `F`: `FRamsey` at `α = 0`, the literal `F` otherwise | defined; **the question is asked about this** |

`G` is not a patch invented here: at `α = 0` it is exactly the value the source's resolution node
declares, and away from `0` it is exactly the literal definition (`G_zero`, `G_of_ne_zero`, both
PROVED, both one line, so the identification is auditable).

**And the two agree for small positive `α`, which is WHY the source's identification is the right
one.**  `F_eq_FRamsey` (PROVED): if `t ≤ n`, `0 < α` and `α\binom nt \le 1`, then
`F t n α = FRamsey t n`.  The reason is that the counts are integers: once `α\binom{|X|}{t} ≤ 1`,
*"at least $\alpha\binom{|X|}{t}$ of each colour"* and *"at least one of each colour"* are the same
condition.  So for each fixed `n` the literal `F t n ·` is CONSTANT on a punctured neighbourhood of
`0`, equal to the Ramsey function there, and the value `0` at `α = 0` is an isolated artefact of
the literal reading.  This is the honest content of "for $\alpha=0$ this is the usual Ramsey
function".

## The second reading question: "increase continuously" cannot be read at fixed `n`

The question sentence says *"For fixed $n,t$ as we change $\alpha$ from $0$ to $1/2$"*.  But
`G t n ·` is `ℕ`-valued and monotone (`F_mono`, PROVED), so at fixed `n` it is continuous exactly
when it is constant, and Erdős's dichotomy ("continuously, or jumps?") would be empty.  The
resolution node settles the reading: every result it records — $\asymp\log_{t-1}n$,
$\gg_\alpha(\log n)^{1/(t-1)}$, $\ll_\alpha\sqrt{\log n}$ — is a statement about the GROWTH RATE
IN `n` of `n ↦ G t n α`, and "a jump" means that growth rate changing as `α` varies.  That is the
reading taken:

* `SameOrder f g` — Erdős's `≍`: each of `f`, `g` is eventually bounded by a constant times the
  other.
* `SameGrowth t α β` — `n ↦ G t n α` and `n ↦ G t n β` have the same order.
* `JumpAt t α₀` — arbitrarily close to `α₀` inside `[0,1/2)` there is a `β` with a different order.
* `NoJumps t` / `ExactlyOneJump t` — the two branches of the source's own dichotomy.
* `Question t := NoJumps t ∨ ExactlyOneJump t`.

⛔ **`Question` is weaker than the prize, and this is the record that it is.**  The source asks
*which* of the two holds; no `Prop` can demand a determination, and the disjunction is the
strongest statement about #161 that names no answer.  (It is not a tautology: three or more jumps
would refute it.)  What Erdős paid \$500 for is the answer, and `ErdosGuess` is what he guessed it
to be.

## Conventions the source leaves unstated (each one NAMED, with the reading taken)

* **A 2-colouring of the edges of the complete `t`-uniform hypergraph on `[n]`** is
  `c : Finset (Fin n) → Bool`.  Only the values of `c` on `t`-subsets of `Fin n` are ever read, so
  colouring the whole powerset is a harmless enlargement of the domain and avoids carrying a
  subtype `{e // #e = t}` through every term.  Vertices are `Fin n`; the labelling is irrelevant
  because `F` is defined by a quantifier over all colourings.
* **"$t$-subsets of $X$"** is `Finset.powersetCard t X`, whose card is `Nat.choose #X t` — so the
  source's $\binom{|X|}{t}$ is literally the number of objects being counted, and
  `colourCount_add` (PROVED) records that the two colour counts sum to it.
* **"at least $\alpha\binom{|X|}{t}$ many"** is a REAL inequality `α * ↑(#X).choose t ≤ ↑count`,
  not a `ℕ` one: `α` is real and the product need not be an integer.  Casting the count up to `ℝ`
  is what makes "at least" mean `≥` and not `≥ ⌈·⌉`.
* **"$X \subseteq [n]$ with $|X| \ge m$"** ranges over ALL such `X`, including `X` with `|X| < t`
  (where both counts are `0` and $\binom{|X|}{t}=0$, so the condition holds) and `X = ∅`.  No
  nonemptiness guard is imposed, because the source imposes none; the degenerate instances are
  computed below rather than assumed away.
* **"the smallest $m$"** is `sInf` over the set of admissible `m`.  ⛔ `Nat.sInf` returns the junk
  value `0` on an EMPTY set.  That is closed: `valid_succ` (PROVED) shows `m = n+1` is always
  admissible — vacuously, since no `X ⊆ Fin n` has `#X ≥ n+1` — so the set is `.Nonempty` and
  `F t n α ≤ n + 1` (`F_le_succ`).  There is no boundedness burden in the other direction, since
  `sInf` of a nonempty set of naturals is its least element.
* **`m` ranges over `ℕ`**, so `m = 0` is allowed; that is what makes `F t n 0 = 0` and not `1`.
* **The threshold is factored through `Valid t n τ m`**, a helper parametric in the threshold
  function `τ : ℕ → ℝ`, so that `F` (with `τ k = α\binom kt`) and `FRamsey` (with `τ ≡ 1`) share
  one definition and therefore share every structural lemma by construction rather than by
  resemblance.  `F`'s own threshold is spelled out in `thr` and nowhere else.
* **`\log_{t-1} n` is read as the `(t-1)`-fold ITERATED logarithm**, `iterLog`, not as the
  logarithm to base `t-1`.  ⛔ The source does not define the subscript.  The base reading is
  untenable on the source's own range: at `t = 2` it would be the logarithm to base `1`, which
  does not exist, whereas the iterated reading gives the ordinary logarithm there.  ⛔ `iterLog`
  iterates `Nat.log 2`; the base of the innermost logarithm is not determined by the source
  either, and it is irrelevant to `≍` for a single logarithm but NOT obviously so under iteration.
  This is why `ErdosHajnalRadoConsequence` is a `def : Prop` and is asserted nowhere.
* **`\gg_\alpha` and `\ll_\alpha`** are unfolded as "there exists a positive constant (allowed to
  depend on everything fixed, here `t` and `α`) such that eventually ...", along `Filter.atTop`.
  The subscripts therefore become the position of the `∃ c` relative to the `∀ α`, which is
  exactly what they mean.

## Degenerate instances — CHECKED BEFORE COMMITTING, each with its actual value

| instance | value | proved by |
|---|---|---|
| `α = 0`, any `t, n` | `F t n 0 = 0` | `F_zero` |
| `α > 0`, `t ≤ n` | `F t n α > t`, so `≥ 1` | `t_lt_F` |
| any `α`, `m = n+1` | admissible, vacuously | `valid_succ` |
| `n < t` | every `X` has `#X ≤ n < t`, so all counts are `0` and all thresholds are `α·0 = 0`: `F t n α = 0` for every `α` | subsumed by `valid_succ` + the `m = 0` witness; NOT separately named, and it is the reason `t_lt_F` carries `t ≤ n` |
| `t = 0` | `Finset.powersetCard 0 X = {∅}`, so every `X` has exactly one `0`-subset and the analysis of `t_lt_F` applies verbatim with `t = 0` | the source's range is `t ≥ 1`; nothing here needs `t ≥ 1` except `iterLog`'s index `t-1` |

⛔ The source's `n,t ≥ 1` is NOT imposed on the definitions, only on the statements that need it.
Imposing it on `F` would have hidden the `t = 0` and `n < t` behaviour rather than recording it.

## Mathlib gaps (checked on the built Mathlib on this machine, `v4.31.0-rc1`)

* **The string "hypergraph" does not occur anywhere in Mathlib** (`grep -rli hypergraph Mathlib`
  returns nothing).  `Mathlib/Combinatorics/` has `SimpleGraph/`, `SetFamily/`, `Colex`,
  `Matroid/`, `Young/`, `Enumerative/` — nothing `t`-uniform for `t > 2`.
* **No Ramsey number and no Ramsey function.**  `FRamsey` is written from scratch.
* **No iterated logarithm.**  `Nat.log` and `Real.log` exist; `iterLog` is defined here.
* `SimpleGraph.extremalNumber` / `IsContained` / `Copy` / `turanDensity` are the `r = 2` case and
  are stated for `SimpleGraph`, whose edge type is `Sym2`; they do not generalise.

## Relation to the sibling artifacts

`erdos-500.lean` and `erdos-712.lean` build `r`-uniform hypergraph machinery for extremal
(Turán-type) questions: a hypergraph is a `Finset (Finset (Fin n))` of `r`-sets and the quantity
is a `sSup` of edge counts.  **That machinery does not transfer here and is deliberately not
copied.**  #161 quantifies over 2-COLOURINGS of the complete hypergraph (a function on `t`-sets),
not over subhypergraphs, and takes an `sInf` of thresholds, not an `sSup` of edge counts.  What IS
reused verbatim in spirit is their representation decision — `t`-edges are `Finset (Fin n)` of card
`t`, vertices are `Fin n`, `Finset.powersetCard t` enumerates the edges — so the three files agree
on what a `t`-uniform edge is, which is the only definition they share.  ⛔ Their `IsCompleteOn`
one-directional-containment discussion (the `SimpleGraph.Embedding` / induced-copy trap) has no
analogue here: there is no containment relation in #161 at all.

## Mathlib used

`Finset.powersetCard` / `Finset.card_powersetCard` / `Finset.mem_powersetCard`,
`Finset.filter` / `Finset.filter_congr` / `Finset.card_filter_add_card_filter_not`,
`Finset.exists_subset_card_eq`, `Finset.card_le_card`, `Finset.subset_univ`, `Finset.card_univ`,
`Fintype.card_fin`, `Nat.choose` / `choose_self` / `choose_pos` / `choose_le_choose`, `Nat.log`,
`sInf` on `ℕ` with `Nat.sInf_le` and `Nat.sInf_mem` (`Mathlib.Data.Nat.Lattice`), `Filter.atTop`,
`Filter.Eventually` / `filter_upwards` / `Filter.eventually_ge_atTop`, `Real.log`, `Real.sqrt`,
`Real.rpow`, `Real.sqrt_eq_rpow`.
-/

-- @category research open
-- @AMS 5
-- Category vocabulary and AMS tagging adopted from the formal-conjectures corpus
-- (509 files, measured 2026-08-28). Written as a comment rather than the corpus
-- attribute form, so this artifact still elaborates standalone, outside their project.










import Mathlib
namespace Erdos161

open Filter

/-! ### Colourings and colour counts -/

/-- `colourCount t c b X` : how many `t`-subsets of `X` receive colour `b` under the 2-colouring
`c` of the edges of the complete `t`-uniform hypergraph.

This is the source's *"$t$-subsets of $X$ of each colour"*, one colour at a time.  A colouring is
a `Finset (Fin n) → Bool`; only its values on `t`-subsets are read. -/
def colourCount (t : ℕ) {n : ℕ} (c : Finset (Fin n) → Bool) (b : Bool)
    (X : Finset (Fin n)) : ℕ :=
  ((Finset.powersetCard t X).filter (fun e => c e = b)).card

/-- Every vertex set has at most `n` vertices.  Used to make `m = n+1` vacuously admissible. -/
theorem card_le_of_finset (n : ℕ) (X : Finset (Fin n)) : X.card ≤ n := by
  have h := Finset.card_le_card (Finset.subset_univ X)
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- **PROVED — the counting identity the whole problem is normalised against.**  The two colour
counts of `X` add up to $\binom{|X|}{t}$, the number of `t`-subsets of `X`.

This is the anti-vacuity control for `colourCount`: it shows the two counts really do partition
the `t`-subsets, so "at least $\alpha\binom{|X|}{t}$ of each colour" is a constraint on a genuine
2-colouring and not on two unrelated quantities. -/
theorem colourCount_add (t : ℕ) {n : ℕ} (c : Finset (Fin n) → Bool) (X : Finset (Fin n)) :
    colourCount t c true X + colourCount t c false X = (X.card).choose t := by
  have hEq : Finset.filter (fun e => c e = false) (Finset.powersetCard t X)
      = Finset.filter (fun e => ¬ (c e = true)) (Finset.powersetCard t X) :=
    Finset.filter_congr (fun e _ => by simp)
  have h := Finset.card_filter_add_card_filter_not
      (s := Finset.powersetCard t X) (p := fun e => c e = true)
  unfold colourCount
  rw [hEq, h, Finset.card_powersetCard]

/-! ### `Valid`, the admissibility of a threshold `m`, and the two functions built from it -/

/-- `Valid t n τ m` : *we can 2-colour the edges of the complete `t`-uniform hypergraph on `n`
vertices such that if `X ⊆ [n]` with `|X| ≥ m` then there are at least `τ |X|` many `t`-subsets of
`X` of each colour.*

Parametric in the threshold `τ : ℕ → ℝ` so that the source's `F` (threshold `α·binom |X| t`) and
the source's *"usual Ramsey function"* (threshold `1`) are the SAME definition at two thresholds,
and therefore share every lemma below by construction. -/
def Valid (t n : ℕ) (τ : ℕ → ℝ) (m : ℕ) : Prop :=
  ∃ c : Finset (Fin n) → Bool, ∀ X : Finset (Fin n), m ≤ X.card →
    τ X.card ≤ (colourCount t c true X : ℝ) ∧ τ X.card ≤ (colourCount t c false X : ℝ)

/-- The source's own threshold: $\alpha\binom{|X|}{t}$, as a real number. -/
def thr (t : ℕ) (α : ℝ) : ℕ → ℝ := fun k => α * (k.choose t : ℝ)

/-- `F t n α` = $F^{(t)}(n,\alpha)$, *the smallest $m$ such that we can $2$-colour the edges of the
complete $t$-uniform hypergraph on $n$ vertices such that if $X\subseteq[n]$ with
$\lvert X\rvert\ge m$ then there are at least $\alpha\binom{\lvert X\rvert}{t}$ many $t$-subsets of
$X$ of each colour* — the LITERAL transcription of the source's definition.

⛔ `Nat.sInf` returns the junk value `0` on an empty set.  That cannot happen: `valid_succ` shows
`n + 1` is always admissible, so the set is nonempty and `sInf` is its least element
(`F_le_succ`).

⛔ At `α = 0` the literal condition is vacuous and this is `0` (`F_zero`), which is NOT the Ramsey
function the source's resolution node describes.  See `G` and the header. -/
noncomputable def F (t n : ℕ) (α : ℝ) : ℕ := sInf {m | Valid t n (thr t α) m}

/-- `FRamsey t n` — *"the usual Ramsey function"* the source says $F^{(t)}(n,0)$ is: the smallest
`m` admitting a 2-colouring in which every `X` with `|X| ≥ m` has at least one `t`-subset of each
colour, i.e. is not monochromatic.

Obtained from `Valid` at the constant threshold `1`, so it is the same object as `F` with the
counting condition replaced by positivity. -/
noncomputable def FRamsey (t n : ℕ) : ℕ := sInf {m | Valid t n (fun _ => 1) m}

/-! ### Well-definedness and the degenerate values — ALL PROVED (no `sorry`) -/

/-- **PROVED.**  `m = n + 1` is always admissible, vacuously: no `X ⊆ Fin n` has `#X ≥ n + 1`.
This is what makes the admissible set nonempty, so `sInf` is a genuine least element and never
`Nat.sInf`'s empty-set junk value. -/
theorem valid_succ (t n : ℕ) (τ : ℕ → ℝ) : Valid t n τ (n + 1) := by
  refine ⟨fun _ => true, fun X hX => ?_⟩
  exfalso
  have hcard := card_le_of_finset n X
  omega

/-- **PROVED.**  The admissible set for `F` is nonempty. -/
theorem validSet_nonempty (t n : ℕ) (τ : ℕ → ℝ) : {m | Valid t n τ m}.Nonempty :=
  ⟨n + 1, valid_succ t n τ⟩

/-- **PROVED.**  `F^{(t)}(n,\alpha) \le n+1`, so the `sInf` is bounded and real. -/
theorem F_le_succ (t n : ℕ) (α : ℝ) : F t n α ≤ n + 1 :=
  Nat.sInf_le (valid_succ t n (thr t α))

/-- **PROVED.**  The same bound for the Ramsey function. -/
theorem FRamsey_le_succ (t n : ℕ) : FRamsey t n ≤ n + 1 :=
  Nat.sInf_le (valid_succ t n (fun _ => 1))

/-- **PROVED — the degeneracy of the literal `α = 0` instance.**  `F t n 0 = 0`.

At `α = 0` the source's condition reads "at least `0` many `t`-subsets of each colour", which every
colouring satisfies for every `X`, so `m = 0` is admissible.  ⛔ This is a REAL zero (the
admissible set is nonempty by `validSet_nonempty`), not `Nat.sInf`'s junk value — and it is the
reason the literal reading cannot be the source's $F^{(t)}(n,0)$. -/
theorem F_zero (t n : ℕ) : F t n 0 = 0 := by
  have hv : Valid t n (thr t 0) 0 := by
    refine ⟨fun _ => true, fun X _ => ⟨?_, ?_⟩⟩
    · simp only [thr, zero_mul]
      exact Nat.cast_nonneg _
    · simp only [thr, zero_mul]
      exact Nat.cast_nonneg _
  exact Nat.le_zero.mp (Nat.sInf_le hv)

/-- **PROVED — the key finiteness obstruction.**  If the threshold is positive at `t` and there are
at least `t` vertices, then every admissible `m` exceeds `t`.

A set `X` of exactly `t` vertices has exactly ONE `t`-subset (namely `X`), which carries a single
colour; the other colour's count is `0`, and `0 ≥ τ t > 0` is false.  So `X` witnesses that no
`m ≤ t` is admissible. -/
theorem lt_of_valid {t n m : ℕ} {τ : ℕ → ℝ} (hτ : 0 < τ t) (htn : t ≤ n)
    (hv : Valid t n τ m) : t < m := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, hc⟩ := hv
  obtain ⟨X, -, hX⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (n := t)
      (by simpa using htn)
  obtain ⟨hr, hb⟩ := hc X (by rw [hX]; exact hcon)
  rw [hX] at hr hb
  have hsum := colourCount_add t c X
  rw [hX, Nat.choose_self] at hsum
  have hr0 : colourCount t c true X ≠ 0 := by
    intro h0
    rw [h0] at hr
    simp only [Nat.cast_zero] at hr
    linarith
  have hb0 : colourCount t c false X ≠ 0 := by
    intro h0
    rw [h0] at hb
    simp only [Nat.cast_zero] at hb
    linarith
  omega

/-- **PROVED.**  For `α > 0` and `t ≤ n`, `t < F^{(t)}(n,\alpha)`.  In particular
`F t n α ≥ 1 > 0 = F t n 0`. -/
theorem t_lt_F {t n : ℕ} {α : ℝ} (hα : 0 < α) (htn : t ≤ n) : t < F t n α := by
  refine lt_of_valid ?_ htn (Nat.sInf_mem (validSet_nonempty t n (thr t α)))
  have h : thr t α t = α := by simp [thr]
  rw [h]
  exact hα

/-- **PROVED.**  The same obstruction for the Ramsey function: `t < FRamsey t n` when `t ≤ n`. -/
theorem t_lt_FRamsey {t n : ℕ} (htn : t ≤ n) : t < FRamsey t n := by
  have hmem : Valid t n (fun _ => (1 : ℝ)) (FRamsey t n) :=
    Nat.sInf_mem (validSet_nonempty t n (fun _ => (1 : ℝ)))
  refine lt_of_valid ?_ htn hmem
  norm_num

/-- **PROVED — the literal function already jumps at `0`, for every fixed `n`.**

`F t n 0 = 0 < F t n α` whenever `α > 0` and `t ≤ n`.  ⛔ This says nothing about Erdős's problem:
it is an artefact of transcribing "at least `0·binom` many" literally.  It is recorded because a
formalization that silently carried this degeneracy would let someone "settle" half of Erdős's
guess without touching the mathematics. -/
theorem literal_jump_at_zero {t n : ℕ} {α : ℝ} (hα : 0 < α) (htn : t ≤ n) :
    F t n 0 < F t n α := by
  have h1 := t_lt_F hα htn
  have h0 := F_zero t n
  omega

/-! ### Monotonicity in `α` -/

/-- **PROVED.**  A larger threshold is a stronger requirement, pointwise. -/
theorem thr_mono {t : ℕ} {α β : ℝ} (h : α ≤ β) (k : ℕ) : thr t α k ≤ thr t β k :=
  mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)

/-- **PROVED.**  Lowering the threshold preserves admissibility. -/
theorem valid_mono {t n m : ℕ} {τ σ : ℕ → ℝ} (h : ∀ k, τ k ≤ σ k)
    (hv : Valid t n σ m) : Valid t n τ m := by
  obtain ⟨c, hc⟩ := hv
  exact ⟨c, fun X hX => ⟨le_trans (h _) (hc X hX).1, le_trans (h _) (hc X hX).2⟩⟩

/-- **PROVED.**  `F^{(t)}(n,\cdot)` is non-decreasing in `α`.

⛔ This is what makes "does $F$ increase continuously" unaskable at fixed `n`: a monotone
`ℕ`-valued function of a real parameter is continuous only where it is locally constant, so at
fixed `n` the dichotomy in the source's question would be empty.  See the header for the
asymptotic reading that is taken instead. -/
theorem F_mono {t n : ℕ} {α β : ℝ} (h : α ≤ β) : F t n α ≤ F t n β :=
  Nat.sInf_le (valid_mono (fun k => thr_mono h k)
    (Nat.sInf_mem (validSet_nonempty t n (thr t β))))

/-! ### Why the source calls the `α = 0` case the Ramsey function: they agree for small `α > 0` -/

/-- **PROVED.**  Once `α\binom nt \le 1`, the source's counting condition and "at least one
`t`-subset of each colour" are the SAME condition on every threshold `m > t`.

The counts are integers: `count ≥ α·binom |X| t` with `0 < α·binom |X| t ≤ 1` says exactly
`count ≥ 1`. -/
theorem valid_iff_of_small {t n m : ℕ} {α : ℝ} (hα : 0 < α)
    (hsmall : α * (n.choose t : ℝ) ≤ 1) (htm : t < m) :
    Valid t n (thr t α) m ↔ Valid t n (fun _ => 1) m := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun X hX => ?_⟩
    have htX : t ≤ X.card := le_of_lt (lt_of_lt_of_le htm hX)
    have hpos : 0 < thr t α X.card :=
      mul_pos hα (by exact_mod_cast Nat.choose_pos htX)
    obtain ⟨hr, hb⟩ := hc X hX
    constructor
    · show (1 : ℝ) ≤ (colourCount t c true X : ℝ)
      have h1 : (0 : ℝ) < (colourCount t c true X : ℝ) := lt_of_lt_of_le hpos hr
      have h2 : 0 < colourCount t c true X := by exact_mod_cast h1
      have h3 : 1 ≤ colourCount t c true X := by omega
      exact_mod_cast h3
    · show (1 : ℝ) ≤ (colourCount t c false X : ℝ)
      have h1 : (0 : ℝ) < (colourCount t c false X : ℝ) := lt_of_lt_of_le hpos hb
      have h2 : 0 < colourCount t c false X := by exact_mod_cast h1
      have h3 : 1 ≤ colourCount t c false X := by omega
      exact_mod_cast h3
  · rintro ⟨c, hc⟩
    refine ⟨c, fun X hX => ?_⟩
    have hle : thr t α X.card ≤ 1 := by
      have hch : (X.card.choose t : ℝ) ≤ (n.choose t : ℝ) := by
        exact_mod_cast Nat.choose_le_choose t (card_le_of_finset n X)
      have hstep : thr t α X.card ≤ α * (n.choose t : ℝ) :=
        mul_le_mul_of_nonneg_left hch (le_of_lt hα)
      linarith
    obtain ⟨hr, hb⟩ := hc X hX
    exact ⟨le_trans hle hr, le_trans hle hb⟩

/-- **PROVED — the identification the source's resolution node asserts.**

For `t ≤ n`, `0 < α` and `α\binom nt \le 1`:  `F^{(t)}(n,\alpha) = ` the usual Ramsey function.

So for each fixed `n` the literal `F t n ·` is CONSTANT on a punctured neighbourhood of `0` and
equal to the Ramsey function there.  ⛔ The value `0` that the literal reading takes AT `α = 0`
(`F_zero`) is therefore an isolated artefact, and the source's sentence "for $\alpha=0$ this is the
usual Ramsey function" is a statement about this limit, not about the literal instance. -/
theorem F_eq_FRamsey {t n : ℕ} {α : ℝ} (htn : t ≤ n) (hα : 0 < α)
    (hsmall : α * (n.choose t : ℝ) ≤ 1) : F t n α = FRamsey t n := by
  have hset : {m | Valid t n (thr t α) m} = {m | Valid t n (fun _ => 1) m} := by
    ext m
    simp only [Set.mem_setOf_eq]
    by_cases hm : t < m
    · exact valid_iff_of_small hα hsmall hm
    · push_neg at hm
      have hτ : 0 < thr t α t := by
        have h : thr t α t = α := by simp [thr]
        rw [h]; exact hα
      constructor
      · intro h
        exact absurd (lt_of_valid hτ htn h) (by omega)
      · intro h
        exact absurd (lt_of_valid (by norm_num) htn h) (by omega)
  unfold F FRamsey
  rw [hset]

/-! ### `G` — the function the source's resolution node is about -/

/-- `G t n α` is the source's $F^{(t)}(n,\alpha)$: the literal definition away from `α = 0`, and
at `α = 0` the value the source's resolution node declares it to have, *"the usual Ramsey
function"*.

⛔ Not an invention: `G_of_ne_zero` and `G_zero` (both PROVED, both immediate) expose exactly which
value is taken where, and `F_eq_FRamsey` (PROVED) is the reason the two clauses agree in the
limit.  Every asymptotic statement below is about `G`. -/
noncomputable def G (t n : ℕ) (α : ℝ) : ℕ := if α = 0 then FRamsey t n else F t n α

/-- **PROVED.**  `G` at `α = 0` is the Ramsey function, as the source declares. -/
theorem G_zero (t n : ℕ) : G t n 0 = FRamsey t n := by simp [G]

/-- **PROVED.**  `G` away from `0` is the literal transcription. -/
theorem G_of_ne_zero {t n : ℕ} {α : ℝ} (h : α ≠ 0) : G t n α = F t n α := by simp [G, h]

/-! ### `≍`, jumps, and THE QUESTION.  Open; no answer is asserted. -/

/-- Erdős's `≍`: `f` and `g` have the same order of growth — each is eventually at most a constant
multiple of the other.  This is the relation in which every statement of the resolution node is
phrased. -/
def SameOrder (f g : ℕ → ℕ) : Prop :=
  (∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ C * (g n : ℝ)) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ C * (f n : ℝ))

/-- **PROVED anti-vacuity control on `SameOrder`:** it is reflexive.  Together with
`not_sameOrder_F_zero` (which exhibits a FAILING pair) this shows the relation is neither
always-true nor always-false. -/
theorem sameOrder_refl (f : ℕ → ℕ) : SameOrder f f := by
  refine ⟨⟨1, one_pos, ?_⟩, ⟨1, one_pos, ?_⟩⟩ <;>
    · filter_upwards with n
      simp

/-- **PROVED.**  `SameOrder` is symmetric. -/
theorem sameOrder_symm {f g : ℕ → ℕ} (h : SameOrder f g) : SameOrder g f := ⟨h.2, h.1⟩

/-- **PROVED — the tool that turns the resolution node's two bounds into a growth-class
statement.**  If `f₁` and `f₂` are both sandwiched between positive multiples of the same `g`, they
have the same order.

⛔ No sign hypothesis on `g` is needed: the constants are combined multiplicatively. -/
theorem sameOrder_of_sandwich {f₁ f₂ : ℕ → ℕ} {g : ℕ → ℝ} {c₁ C₁ c₂ C₂ : ℝ}
    (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hc₂ : 0 < c₂) (hC₂ : 0 < C₂)
    (h1lo : ∀ᶠ n : ℕ in atTop, c₁ * g n ≤ (f₁ n : ℝ))
    (h1hi : ∀ᶠ n : ℕ in atTop, (f₁ n : ℝ) ≤ C₁ * g n)
    (h2lo : ∀ᶠ n : ℕ in atTop, c₂ * g n ≤ (f₂ n : ℝ))
    (h2hi : ∀ᶠ n : ℕ in atTop, (f₂ n : ℝ) ≤ C₂ * g n) :
    SameOrder f₁ f₂ := by
  constructor
  · refine ⟨C₁ / c₂, by positivity, ?_⟩
    filter_upwards [h1hi, h2lo] with n ha hb
    have hmul : C₁ / c₂ * (c₂ * g n) = C₁ * g n := by field_simp
    have hstep : C₁ / c₂ * (c₂ * g n) ≤ C₁ / c₂ * (f₂ n : ℝ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    linarith
  · refine ⟨C₂ / c₁, by positivity, ?_⟩
    filter_upwards [h2hi, h1lo] with n ha hb
    have hmul : C₂ / c₁ * (c₁ * g n) = C₂ * g n := by field_simp
    have hstep : C₂ / c₁ * (c₁ * g n) ≤ C₂ / c₁ * (f₁ n : ℝ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    linarith

/-- **PROVED — the asymptotic face of the `α = 0` degeneracy.**  Under the LITERAL reading,
`n ↦ F t n 0` is identically zero, hence not `≍` to `n ↦ F t n α` for any `α > 0`, whatever those
functions do.

⛔ So had the question been stated over `F` rather than over `G`, "there is a jump at `0`" would
have been a one-line theorem, and Erdős's guess would be half-settled by a transcription artefact.
This lemma is why `G` exists. -/
theorem not_sameOrder_F_zero {t : ℕ} {α : ℝ} (hα : 0 < α) :
    ¬ SameOrder (fun n => F t n 0) (fun n => F t n α) := by
  rintro ⟨-, C, -, hev⟩
  obtain ⟨n, hn, hnt⟩ := (hev.and (eventually_ge_atTop t)).exists
  simp only [F_zero, Nat.cast_zero, mul_zero] at hn
  have hpos : t < F t n α := t_lt_F hα hnt
  have hcast : (0 : ℝ) < (F t n α : ℝ) := by
    have : 0 < F t n α := by omega
    exact_mod_cast this
  linarith

/-- `SameGrowth t α β` : the two parameters give the same growth order in `n`. -/
def SameGrowth (t : ℕ) (α β : ℝ) : Prop :=
  SameOrder (fun n => G t n α) (fun n => G t n β)

/-- The source's parameter range `\alpha\in[0,1/2)`. -/
def InRange (α : ℝ) : Prop := 0 ≤ α ∧ α < 1 / 2

/-- `JumpAt t α₀` : the growth order is discontinuous at `α₀` — arbitrarily close to `α₀`, inside
the source's range, there is a parameter with a DIFFERENT growth order.

This is the reading of the source's *"are there jumps?"*; see the header for why the fixed-`n`
reading is empty. -/
def JumpAt (t : ℕ) (α₀ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ β : ℝ, InRange β ∧ |β - α₀| < δ ∧ ¬ SameGrowth t α₀ β

/-- *"does $F^{(t)}(n,\alpha)$ increase continuously"* — the first branch of the source's
dichotomy: no jump anywhere in `[0,1/2)`. -/
def NoJumps (t : ℕ) : Prop := ∀ α : ℝ, InRange α → ¬ JumpAt t α

/-- *"Only one jump?"* — the second branch. -/
def ExactlyOneJump (t : ℕ) : Prop := ∃! α : ℝ, InRange α ∧ JumpAt t α

/-- **Erdős #161 (OPEN, \$500).**  *"For fixed $n,t$ as we change $\alpha$ from $0$ to $1/2$ does
$F^{(t)}(n,\alpha)$ increase continuously or are there jumps? Only one jump?"*

Formalised as the source's own dichotomy: either there are no jumps at all, or there is exactly
one.

A `def`, not a `theorem`: the problem is open and this file takes no position.  ⛔ See the header
for the honest gap — the source asks WHICH branch holds, and no `Prop` can demand a determination;
this disjunction is the strongest statement about #161 that names no answer.  It is not a
tautology: two or more jumps refute it. -/
def Question (t : ℕ) : Prop := NoJumps t ∨ ExactlyOneJump t

/-- **Erdős's guess (a GUESS, never a theorem).**  The source: *"If I can hazard a guess completely
unsupported by evidence, I am afraid that the jump occurs all in one step at $0$."*

A `def : Prop`.  ⛔ The source itself calls this unsupported, and adds *"It would be much more
interesting if my conjecture would be wrong and perhaps there is some hope for this for $t>3$"* —
so the `t` here is not universally quantified anywhere in this file. -/
def ErdosGuess (t : ℕ) : Prop :=
  JumpAt t 0 ∧ ∀ α : ℝ, 0 < α → α < 1 / 2 → ¬ JumpAt t α

/-- **PROVED.**  Erdős's guess is a strengthening of the "only one jump" branch, not a
restatement: it also says WHERE the jump is.  Pure bookkeeping over this file's own definitions,
recorded so the two are not read as independent. -/
theorem erdosGuess_imp_exactlyOneJump {t : ℕ} (h : ErdosGuess t) : ExactlyOneJump t := by
  refine ⟨0, ⟨⟨le_refl 0, by norm_num⟩, h.1⟩, ?_⟩
  rintro y ⟨⟨hy0, hy2⟩, hyj⟩
  rcases eq_or_lt_of_le hy0 with heq | hlt
  · exact heq.symm
  · exact absurd hyj (h.2 y hlt hy2)

/-- **PROVED.**  Erdős's guess answers the question (in the "only one jump" branch). -/
theorem erdosGuess_imp_question {t : ℕ} (h : ErdosGuess t) : Question t :=
  Or.inr (erdosGuess_imp_exactlyOneJump h)

/-! ### The iterated logarithm, and the conditional statement the source attributes to
Erdős–Hajnal–Rado -/

/-- The `k`-fold iterated logarithm, `iterLog k n = log log … log n` with `k` logarithms.

⛔ READING DECLARED: the source writes `\log_{t-1} n` and does not define the subscript.  The
"logarithm to base `t-1`" reading is untenable on the source's own range `t ≥ 1`: at `t = 2` it
would be the logarithm to base `1`.  The iterated reading gives the ordinary logarithm there, and
is the standard meaning in this Ramsey context.  ⛔ The base of the innermost logarithm (`2` here)
is not determined by the source; it is irrelevant to `≍` for one logarithm but not obviously so
under iteration, which is one reason the statement below is a `def` and not a theorem. -/
def iterLog : ℕ → ℕ → ℕ
  | 0, n => n
  | (k + 1), n => Nat.log 2 (iterLog k n)

/-- **PROVED anti-vacuity control on `iterLog`:** it really iterates.  `iterLog 0` is the identity
and `iterLog 2 65536 = 4`, computed by the kernel — so the definition is neither the identity in
disguise nor constant. -/
theorem iterLog_two_65536 : iterLog 2 65536 = 4 := by decide

/-- **The consequence the source attributes to a conjecture of Erdős, Hajnal and Rado:**
\[F^{(t)}(n,0)\asymp \log_{t-1} n.\]

⛔ A `def : Prop`, asserted nowhere.  Two independent reasons: the source states it only as a
CONSEQUENCE of a conjecture it does not spell out (it points at entry [562]), so the conjecture
itself is not formalized here and cannot be — and the reading of `\log_{t-1}` is the declared one
above, not a given.  ⛔ It is stated about `FRamsey`, because that is what the source's
$F^{(t)}(n,0)$ is; the literal `F t n 0` is `0` (`F_zero`). -/
def ErdosHajnalRadoConsequence (t : ℕ) : Prop :=
  SameOrder (fun n => FRamsey t n) (fun n => iterLog (t - 1) n)

/-! ### What the resolution node records as KNOWN.  Stated with `sorry`, not proved here. -/

/-- The source's $(\log n)^{1/(t-1)}$, which at `t = 3` is its $\sqrt{\log n}$
(`logPow_three`, PROVED). -/
noncomputable def logPow (t : ℕ) (n : ℕ) : ℝ := (Real.log n) ^ (1 / ((t : ℝ) - 1))

/-- **PROVED — the transcription check.**  `logPow 3 n` really is the source's $\sqrt{\log n}$, so
the two displayed bounds below are stated against the same function and the corollary that combines
them is not comparing two different quantities. -/
theorem logPow_three (n : ℕ) : logPow 3 n = Real.sqrt (Real.log n) := by
  rw [logPow, Real.sqrt_eq_rpow]
  norm_num

/-- **The lower bound the resolution node records (Erdős and Spencer).**
\[F^{(t)}(n,\alpha) \gg_\alpha (\log n)^{\frac{1}{t-1}} \quad\text{for all } \alpha>0.\]

The `\gg_\alpha` is unfolded as an existential constant depending on `t` and `α`, along `atTop`.
⛔ `t ≥ 2` is required for the exponent `1/(t-1)` to be defined; the source's own display carries
the same requirement implicitly. -/
theorem erdosSpencer_lower_bound (t : ℕ) (ht : 2 ≤ t) (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * logPow t n ≤ (G t n α : ℝ) := by
  sorry

/-- **The upper bound the resolution node records (Conlon, Fox and Sudakov, `CFS11`).**
\[F^{(3)}(n,\alpha) \ll_\alpha \sqrt{\log n} \quad\text{for any fixed } \alpha>0.\]

Stated against `logPow 3`, which `logPow_three` PROVES equals $\sqrt{\log n}$. -/
theorem conlonFoxSudakov_upper_bound (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (G 3 n α : ℝ) ≤ C * logPow 3 n := by
  sorry

/-- **The weaker general-`t` lower bound the resolution node records.**
\[F^{(t)}(n,\alpha)\gg_t (\log n)^{c_\alpha} \quad\text{for all } \alpha>0.\]

⛔ The source names neither `c_α` nor the implied constant, so both are existentially quantified —
`c_α` depending on `α` and the constant on `t` and `α`, which is what the subscripts say. -/
theorem logPower_lower_bound (t : ℕ) (ht : 2 ≤ t) (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, C * (Real.log n) ^ c ≤ (G t n α : ℝ) := by
  sorry

/-- ⛔ NOT FORMALIZED, and the omission is deliberate: the resolution node's *"and a similar upper
bound holds for $\alpha$ close to $1/2$"* names neither the bound nor how close is close.  An
artifact may not supply a formula its frozen source withholds. -/
def UpperBoundNearHalf_NOT_STATED : Prop := True

/-! ### The one consequence the resolution node draws, PROVED from the two bounds above -/

/-- **PROVED (no `sorry` of its own).**  For `t = 3`, ALL parameters `α ∈ (0,1/2)` lie in a single
growth class: the Erdős–Spencer lower bound and the Conlon–Fox–Sudakov upper bound sandwich
`n ↦ G 3 n α` between positive multiples of the same `logPow 3`, for every such `α`.

This is the source's *"Coupled with the lower bound above, this implies that there is only one
jump for fixed $\alpha$ when $t=3$"*, in its unconditional half.

⛔ Its truth rests on `erdosSpencer_lower_bound` and `conlonFoxSudakov_upper_bound`, which are
`sorry`-carrying statements of the literature; the DERIVATION is machine-checked, the inputs are
not. -/
theorem t_three_single_growth_class {α β : ℝ} (hα : 0 < α) (hα2 : α < 1 / 2)
    (hβ : 0 < β) (hβ2 : β < 1 / 2) : SameGrowth 3 α β := by
  obtain ⟨c₁, hc₁, h1lo⟩ := erdosSpencer_lower_bound 3 (by norm_num) α hα hα2
  obtain ⟨C₁, hC₁, h1hi⟩ := conlonFoxSudakov_upper_bound α hα hα2
  obtain ⟨c₂, hc₂, h2lo⟩ := erdosSpencer_lower_bound 3 (by norm_num) β hβ hβ2
  obtain ⟨C₂, hC₂, h2hi⟩ := conlonFoxSudakov_upper_bound β hβ hβ2
  exact sameOrder_of_sandwich hc₁ hC₁ hc₂ hC₂ h1lo h1hi h2lo h2hi

/-- **PROVED (no `sorry` of its own).**  For `t = 3` there is no jump at any `α₀ ∈ (0,1/2)`:
choosing `δ = α₀` forces the nearby parameter to be positive, and all positive parameters share
one growth class.

⛔ The companion claim — that there IS a jump at `0` when `t = 3` — is NOT proved here and cannot
be from this source: it needs the order of `F^{(3)}(n,0)`, which the resolution node supplies only
as a consequence of the unstated Erdős–Hajnal–Rado conjecture (see
`ErdosHajnalRadoConsequence`). -/
theorem t_three_no_jump_pos {α₀ : ℝ} (h0 : 0 < α₀) (h2 : α₀ < 1 / 2) : ¬ JumpAt 3 α₀ := by
  intro hj
  obtain ⟨β, ⟨hβ0, hβ2⟩, hclose, hne⟩ := hj α₀ h0
  rw [abs_lt] at hclose
  exact hne (t_three_single_growth_class h0 h2 (by linarith [hclose.1]) hβ2)

/-! ### Axiom footprints of the fully proved declarations.

Re-checked on every compile rather than recorded once.  Clean is
`[propext, Classical.choice, Quot.sound]`; `sorryAx` would mean NOT PROVED.  ⛔ The two `t_three_*`
corollaries are deliberately NOT printed here: they are `sorry`-free themselves but depend on the
two sorried literature bounds, so their footprint contains `sorryAx` by design. -/

#print axioms colourCount_add
#print axioms valid_succ
#print axioms F_le_succ
#print axioms F_zero
#print axioms lt_of_valid
#print axioms t_lt_F
#print axioms t_lt_FRamsey
#print axioms literal_jump_at_zero
#print axioms F_mono
#print axioms valid_iff_of_small
#print axioms F_eq_FRamsey
#print axioms G_zero
#print axioms G_of_ne_zero
#print axioms sameOrder_refl
#print axioms sameOrder_of_sandwich
#print axioms not_sameOrder_F_zero
#print axioms iterLog_two_65536
#print axioms logPow_three
#print axioms erdosGuess_imp_exactlyOneJump
#print axioms erdosGuess_imp_question

end Erdos161
