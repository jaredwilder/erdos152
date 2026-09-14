/-
# Erdős problem 146 — the Erdős–Simonovits degenerate Turán conjecture

STATUS: **OPEN**. Prize $500. This file states the CONJECTURE as a `def ... : Prop`, and states
the results the source records as KNOWN as separate, individually named, `sorry`-carrying
theorems. ⛔ The conjecture is deliberately NOT a sorried theorem: a sorried theorem is
indistinguishable, to `grep` and to a reader skimming declaration names, from an established
result, and keeping those two apart is this file's entire job.

--------------------------------------------------------------------------------------------
SOURCE (frozen), `entry-graph-erdos-146.json`, node `n000-question` (kind: question), VERBATIM:

  "If $H$ is bipartite and is $r$-degenerate, that is, every induced subgraph of $H$ has minimum
   degree $\leq r$, then \[\mathrm{ex}(n;H) \ll n^{2-1/r}.\]"

SOURCE node `n001-resolution` (kind: resolution), VERBATIM:

  "Conjectured by Erd\H{o}s and Simonovits \cite{ErSi84}. Open even for $r=2$. Alon,
   Krivelevich, and Sudakov \cite{AKS03} have proved \[\mathrm{ex}(n;H) \ll n^{2-1/4r}.\]
   They also prove the full Erd\H{o}s-Simonovits conjectured bound if $H$ is bipartite and the
   maximum degree in one side of the bipartition is $r$. See also [113] and [147] . This problem
   is #43 in Extremal Graph Theory in the graphs problem collection."

--------------------------------------------------------------------------------------------
WHAT IS CONJECTURED VERSUS WHAT IS KNOWN — KEPT APART, DELIBERATELY.

  * `Erdos146.ConjectureAt r`  — the conjecture at a fixed degeneracy `r`, a `Prop`, NOT a
                                 theorem.
  * `Erdos146.Conjecture`      — the conjecture, quantified over all `r ≥ 1`. NOT a theorem.
  * `Erdos146.Conjecture_r_two`— the `r = 2` instance, which the source says is itself open.
  * `alon_krivelevich_sudakov` — KNOWN: the weaker exponent `2 - 1/(4r)`.
  * `alon_krivelevich_sudakov_one_sided`
                               — KNOWN: the full conjectured exponent under the stronger
                                 hypothesis of bounded degree on ONE side of the bipartition.
  * `alon_krivelevich_sudakov_implies_conjecture_of_...` — not stated; there is no such
                                 implication, and the gap between `2 - 1/(4r)` and `2 - 1/r`
                                 IS the open problem.

--------------------------------------------------------------------------------------------
CONVENTIONS NAMED — every one the source leaves unstated, with the reading taken and defended.

(1) ⭐ "COPY" MEANS SUBGRAPH, **NOT** INDUCED SUBGRAPH. This is the single most consequential
    convention in the file, and the induced reading makes the conjecture FALSE.
    Counterexample to the induced reading, at `r = 1`: let `H = P₄`, the path on four vertices.
    Every induced subgraph of `P₄` has a vertex of degree `≤ 1`, so `P₄` is `1`-degenerate, and
    `P₄` is bipartite. The conjecture would give `ex(n; P₄) ≪ n^{2-1/1} = n`. But the complete
    bipartite graph `K_{n/2,n/2}` has `n²/4` edges and contains NO INDUCED `P₄` (every induced
    subgraph of a complete bipartite graph is complete bipartite, and `P₄` is not), so the
    induced-Turán number is `≫ n²`. Hence: `ex(n;H)` here is the ordinary Turán number,
    counting `H` as a not-necessarily-induced subgraph. Mathlib's `SimpleGraph.extremalNumber`
    is exactly this, because Mathlib's `SimpleGraph.Copy` is an INJECTIVE HOMOMORPHISM
    (`toHom : A →g B`, `injective'`) — adjacency is preserved forwards only, non-edges of `H`
    may be edges of `G`. See TRAP A below for the near-miss.

(2) `ex(n;H)` = `SimpleGraph.extremalNumber n H` = the maximum of `#G.edgeFinset` over
    `G : SimpleGraph (Fin n)` with `H.Free G`, i.e. with `¬ (H ⊑ G)`. Vertex set `Fin n` is
    Mathlib's choice and is immaterial: `extremalNumber_of_fintypeCard_eq` transports it along
    any equivalence. If every `n`-vertex graph contains `H`, the value is `0` (a genuine
    maximum over a set containing the empty graph is impossible, so Mathlib's `Finset.sup`
    returns `⊥ = 0`); no statement below reads that regime, since all are eventual in `n`.

(3) `r`-DEGENERATE, EXACTLY AS THE SOURCE DEFINES IT: "every induced subgraph of `H` has
    minimum degree `≤ r`". An induced subgraph is named by its vertex set `S`; its minimum
    degree is `≤ r` exactly when SOME vertex of `S` has `≤ r` neighbours inside `S`. Hence
    `IsDegenerate r H := ∀ S, S.Nonempty → ∃ v ∈ S, (H.neighborSet v ∩ S).ncard ≤ r`.
      * `S.Nonempty` is REQUIRED. The minimum degree of the empty graph is a minimum over an
        empty set — undefined, conventionally `+∞`. Dropping the guard would make the condition
        read `∃ v ∈ ∅, ...`, which is FALSE, so NO graph would be `r`-degenerate and the
        conjecture would be vacuously true. The guard is load-bearing, not cosmetic.
      * INDUCED vs. ARBITRARY subgraph in the degeneracy definition does NOT matter (unlike
        (1)): deleting edges only lowers degrees, so a vertex of degree `≤ r` in an induced
        subgraph is still of degree `≤ r` in any subgraph on the same vertices. The source's
        "induced" and the textbook "every subgraph" definitions of degeneracy agree. We follow
        the source's wording literally.
      * Degrees are counted INSIDE `S`: `H.neighborSet v ∩ S`. Counting `H.neighborSet v` would
        be the degree in `H`, i.e. bounded maximum degree — a strictly stronger and different
        hypothesis (it is, in fact, close to the hypothesis of the KNOWN one-sided result).

(4) `H` IS FINITE. The source's `H` is a fixed finite forbidden graph. `[Fintype W]` is
    therefore assumed wherever `IsDegenerate` appears. Without it the definition is broken
    rather than merely more general: `Set.ncard` of an INFINITE set is `0` by convention, so
    an infinite-degree vertex would report degree `0 ≤ r` and every infinite graph would be
    `0`-degenerate.

(5) `≪` IS VINOGRADOV, spelled out: `f ≪ g` means there exists `C > 0` such that `f n ≤ C * g n`
    for all sufficiently large `n` (`Filter.atTop`). It is `f = O(g)` for eventually-nonnegative
    `f, g`. The eventual guard matters: `n^(2-1/r)` is `0` at `n = 0`, and `ex(0;H) = 0` too, so
    nothing breaks at `0` here — but the guard is the honest reading of `≪` and is kept.

(6) `r ≥ 1`. The source writes `n^{2-1/r}` and so presupposes `r ≥ 1`. In Lean `1/(0:ℝ) = 0`,
    so `r = 0` would silently read as the trivial bound `ex(n;H) ≪ n²`; the hypothesis
    `1 ≤ r` is stated to prevent that junk instance from being smuggled in as content.

(7) `n^(2 - 1/r)` IS A REAL POWER, `Real.rpow`, since the exponent `2 - 1/r` is not an integer
    for `r ≥ 2`. `(0:ℝ) ^ (x:ℝ) = 0` for `x ≠ 0`, which is the intended value at `n = 0`.

(8) "THE MAXIMUM DEGREE IN ONE SIDE OF THE BIPARTITION IS `r`" (the KNOWN one-sided result) is
    read as `≤ r`, not `= r`. Defence: a Turán-type upper bound proved for maximum degree
    exactly `r` immediately gives the same bound for maximum degree `≤ r` (a graph of max
    degree `< r` on one side is a subgraph of one with max degree `r`, and Turán numbers are
    monotone under subgraph containment), so the two readings define the same theorem; `≤` is
    the usable form. The bipartition is witnessed by `SimpleGraph.IsBipartiteWith s t`, and the
    degree bound is imposed on the side `s`.

(9) BINDER ORDER in `ConjectureAt`: `r` outermost (the exponent depends on `r` only), then the
    vertex type `W`, the graph `H`, and its hypotheses; the Vinogradov constant `C` is chosen
    AFTER `H`, i.e. `C = C(H)`. This is the correct strength: a single constant working for all
    `H` at once is false already for `H = K_{r,r}` families as `|H|` grows.

--------------------------------------------------------------------------------------------
MATHLIB TRAPS FOUND AND AVOIDED (Mathlib checked directly, 2026-08-28).

TRAP A (the one that matters). `SimpleGraph.Embedding` (`H ↪g G`) is a `RelEmbedding`, so its
  defining condition is `G.Adj (f u) (f v) ↔ H.Adj u v` — an IFF. That is an INDUCED copy, and
  using it would state the false induced-Turán problem of convention (1). The right notion is
  `SimpleGraph.Copy` (injective `→g`, one direction), which is what `IsContained`/`⊑`/`Free`
  and hence `extremalNumber` are built on. `isContained_of_embedding` below records the
  one-way implication as a PROVED lemma so the direction of the weakening is on the record.

TRAP B (inherited, already paid for by sibling file erdos-182). `SimpleGraph.IsSubgraph`, the
  `≤` on `SimpleGraph V`, is a SPANNING notion over the SAME vertex type. It cannot express
  "`G` contains a copy of `H`" for `H` on a different (smaller) vertex type at all.
  `IsContained.of_le` below records that `≤` is strictly stronger than `⊑`.

TRAP C. Mathlib has NO `SimpleGraph.Subgraph.IsRegularOfDegree`, and no degeneracy predicate at
  all: `SimpleGraph.IsRegularOfDegree` exists only for `SimpleGraph` and needs `[LocallyFinite]`.
  Checked by reading `Mathlib/Combinatorics/SimpleGraph/` directly — there is no `degeneracy`,
  no `IsDegenerate`, no `coreNumber`. So `IsDegenerate` is defined here, from the source's own
  words, on top of Mathlib's `neighborSet` and `Set.ncard`.

TRAP D. `Set.ncard` of an infinite set is `0`, not `⊤`. See convention (4); handled by
  `[Fintype W]`.

MATHLIB DOES HAVE, and this file uses rather than re-derives:
  `SimpleGraph.extremalNumber`, `SimpleGraph.IsContained` (`⊑`), `SimpleGraph.Free`,
  `SimpleGraph.Copy`, `SimpleGraph.IsBipartite` (= `Colorable 2`),
  `SimpleGraph.IsBipartiteWith`, `SimpleGraph.card_edgeFinset_le_card_choose_two`.
-/

-- @category research open
-- @AMS 5
-- Category vocabulary and AMS tagging adopted from the
-- formal-conjectures corpus (509 files, measured 2026-08-28). Written as a comment
-- rather than the corpus attribute form, so this artifact still elaborates
-- standalone, outside their project.







import Mathlib
open Filter SimpleGraph

namespace Erdos146

universe u

variable {W : Type u}

/-! ### `≪` : Vinogradov -/

/-- `VinogradovLE f g` is the source's `f \ll g`: there is a constant `C > 0` with
`f n ≤ C * g n` for all sufficiently large `n`. Convention (5). -/
def VinogradovLE (f g : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, f n ≤ C * g n

/-- The right-hand scale `n^{2 - 1/r}` of the conjecture. A REAL power (`Real.rpow`), since the
exponent is not an integer for `r ≥ 2`. Convention (7). -/
noncomputable def scale (r : ℕ) (n : ℕ) : ℝ := (n : ℝ) ^ (2 - 1 / (r : ℝ))

/-! ### `ex(n;H)` : the Turán number -/

/-- `ex n H` is the Turán number `\mathrm{ex}(n;H)`: the maximum number of edges of a graph on
`n` vertices containing NO COPY of `H`, where a copy is an injective homomorphism, i.e. a
not-necessarily-induced subgraph isomorphic to `H` (convention (1)).

This is `SimpleGraph.extremalNumber`, unchanged; the abbreviation exists only to fix the
argument order used in the statements below and to carry this docstring. -/
noncomputable def ex (n : ℕ) (H : SimpleGraph W) : ℕ := SimpleGraph.extremalNumber n H

/-- `ex` as a real-valued function of `n`, for use on the left of `≪`. -/
noncomputable def exR (H : SimpleGraph W) (n : ℕ) : ℝ := (ex n H : ℝ)

/-! ### `r`-degenerate, exactly as the source defines it -/

/-- `IsDegenerate r H` : *"every induced subgraph of `H` has minimum degree `≤ r`"*.

An induced subgraph is named by its vertex set `S`; its minimum degree is `≤ r` exactly when
some vertex of `S` has at most `r` neighbours INSIDE `S`. The nonemptiness guard on `S` is
mandatory — see convention (3). -/
def IsDegenerate (r : ℕ) (H : SimpleGraph W) : Prop :=
  ∀ S : Set W, S.Nonempty → ∃ v ∈ S, (H.neighborSet v ∩ S).ncard ≤ r

/-! ### PROVED controls — no `sorry`.

These exist so that the definitions above are falsifiable by compilation rather than merely
elaborating. Every one of them exercises a definition introduced in this file. -/

/-- **Control (proved).** `ex(n;H) ≤ binom(n,2)`: a Turán number never exceeds the number of
edges of the complete graph. Exercises `ex`, and pins down that `extremalNumber n H` really is
a count of edges on `n` vertices. -/
theorem ex_le_choose_two (n : ℕ) (H : SimpleGraph W) : ex n H ≤ n.choose 2 := by
  have h : SimpleGraph.extremalNumber (Fintype.card (Fin n)) H ≤ n.choose 2 := by
    rw [SimpleGraph.extremalNumber_le_iff]
    intro G _ _
    simpa using G.card_edgeFinset_le_card_choose_two
  simpa [ex] using h

/-- **Control (proved).** `ex(0;H) = 0`. The degenerate case of the definition. -/
theorem ex_zero (H : SimpleGraph W) : ex 0 H = 0 := by
  have := ex_le_choose_two 0 H
  simpa using this

/-- **Control (proved).** The edgeless graph is `r`-degenerate for every `r`, in particular
`0`-degenerate. Exercises `IsDegenerate` on its extreme case. -/
theorem bot_isDegenerate (r : ℕ) : IsDegenerate r (⊥ : SimpleGraph W) := by
  rintro S ⟨v, hv⟩
  refine ⟨v, hv, ?_⟩
  have hn : (⊥ : SimpleGraph W).neighborSet v = ∅ := by
    ext w; simp [SimpleGraph.neighborSet]
  simp [hn]

/-- **Control (proved).** Degeneracy is monotone in `r`. -/
theorem IsDegenerate.mono {r s : ℕ} {H : SimpleGraph W} (h : r ≤ s) (hd : IsDegenerate r H) :
    IsDegenerate s H := by
  intro S hS
  obtain ⟨v, hv, hle⟩ := hd S hS
  exact ⟨v, hv, hle.trans h⟩

/-- **Control (proved), and TRAP A on the record.** An INDUCED copy is a copy: a graph
embedding (`↪g`, whose defining condition is an *iff* on adjacency) yields a `SimpleGraph.Copy`
(an injective homomorphism, adjacency preserved forwards only).

The converse FAILS, which is exactly why `ex` here is the ordinary and not the induced Turán
number: `H`-freeness in the sense used by `extremalNumber` is the STRONGER hypothesis, so the
ordinary Turán number is the SMALLER quantity, and the conjecture below is the sharper
statement. See convention (1) for the `P₄` / `K_{n/2,n/2}` witness that the induced version of
the conjecture is false. -/
theorem isContained_of_embedding {V : Type u} {H : SimpleGraph W} {G : SimpleGraph V}
    (f : H ↪g G) : H ⊑ G :=
  ⟨f.toCopy⟩

/-- **Control (proved), and TRAP B on the record.** The spanning `≤` on `SimpleGraph V`
(`SimpleGraph.IsSubgraph`) implies containment, so `≤` is strictly stronger than `⊑` and cannot
be the notion in `ex`: `≤` cannot even be typed when `H` lives on a smaller vertex type. -/
theorem isContained_of_le {V : Type u} {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) : G₁ ⊑ G₂ :=
  SimpleGraph.IsContained.of_le h

/-- **Control (proved).** Bounded degree on ONE side of a bipartition forces `r`-degeneracy.

This is the bridge between the hypothesis of the KNOWN result
(`alon_krivelevich_sudakov_one_sided`) and the hypothesis of the CONJECTURE: the known result's
hypothesis is strictly stronger, which is precisely why it does not settle the conjecture.
Proved, not assumed. -/
theorem isDegenerate_of_isBipartiteWith [Fintype W] {H : SimpleGraph W} {s t : Set W} {r : ℕ}
    (hb : H.IsBipartiteWith s t) (hdeg : ∀ v ∈ s, (H.neighborSet v).ncard ≤ r) :
    IsDegenerate r H := by
  rintro S ⟨v, hv⟩
  by_cases hex : ∃ u ∈ S, u ∈ s
  · obtain ⟨u, huS, hus⟩ := hex
    refine ⟨u, huS, le_trans ?_ (hdeg u hus)⟩
    exact Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
  · push Not at hex
    refine ⟨v, hv, ?_⟩
    have hempty : H.neighborSet v ∩ S = ∅ := by
      ext w
      simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hadj hwS
      rcases hb.mem_of_adj hadj with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hex v hv h1
      · exact hex w hwS h2
    simp [hempty]

/-! ### ⭐ THE CONJECTURE. ⛔ `def ... : Prop`, NOT a theorem. -/

/-- **Erdős–Simonovits degenerate Turán conjecture, at a fixed degeneracy `r`.**

  *"If $H$ is bipartite and is $r$-degenerate, that is, every induced subgraph of $H$ has
   minimum degree $\leq r$, then $\mathrm{ex}(n;H) \ll n^{2-1/r}$."*

⛔ THIS IS A CONJECTURE. Nothing in this file asserts it, and it is not stated as a theorem —
not even a sorried one — precisely so that it cannot be mistaken for a result. The constant
implicit in `≪` is allowed to depend on `H` (convention (9)); `r ≥ 1` by convention (6). -/
def ConjectureAt (r : ℕ) : Prop :=
  1 ≤ r → ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
    H.IsBipartite → IsDegenerate r H → VinogradovLE (exR H) (scale r)

/-- **Erdős–Simonovits degenerate Turán conjecture** (Erdős–Simonovits 1984), the full
statement, quantified over the degeneracy `r`. Prize $500. ⛔ OPEN; a `Prop`, not a theorem. -/
def Conjecture : Prop := ∀ r : ℕ, ConjectureAt.{u} r

/-- *"Open even for $r=2$."* — the source. Recorded as its own `Prop` because the source
singles it out as the smallest unsettled case. ⛔ OPEN; a `Prop`, not a theorem.

(The case `r = 1` is not claimed here to be settled either way; the source only says that `r=2`
is open, and this file does not extrapolate.) -/
def Conjecture_r_two : Prop := ConjectureAt.{u} 2

/-- **Proved.** The full conjecture implies its `r = 2` instance. Stated as an implication so
that the logical relationship is machine-readable WITHOUT either side being asserted. -/
theorem conjecture_implies_r_two : Conjecture.{u} → Conjecture_r_two.{u} :=
  fun h => h 2

/-! ### KNOWN — what the resolution node records, each as its own named theorem.

Proofs are `sorry`: these are cited literature results, not results of this file. -/

/-- **Alon, Krivelevich and Sudakov (2003)**, *Turán numbers of bipartite graphs and related
Ramsey-type questions*.

  *"Alon, Krivelevich, and Sudakov \cite{AKS03} have proved
   $\mathrm{ex}(n;H) \ll n^{2-1/4r}$."*

The exponent is `2 - 1/(4r)`, weaker than the conjectured `2 - 1/r`. The gap between the two
exponents IS the open problem; no implication from this theorem to `Conjecture` exists or is
claimed. -/
theorem alon_krivelevich_sudakov (r : ℕ) (hr : 1 ≤ r) (W : Type u) [Fintype W]
    (H : SimpleGraph W) (hb : H.IsBipartite) (hd : IsDegenerate r H) :
    VinogradovLE (exR H) (scale (4 * r)) := by
  sorry

/-- **Alon, Krivelevich and Sudakov (2003), the one-sided case.**

  *"They also prove the full Erd\H{o}s-Simonovits conjectured bound if $H$ is bipartite and the
   maximum degree in one side of the bipartition is $r$."*

Here the conclusion IS the conjectured `n^{2-1/r}`, but the hypothesis is strictly stronger:
maximum degree `≤ r` on one side (convention (8)), rather than `r`-degeneracy. That the
hypothesis really is stronger is PROVED above, in `isDegenerate_of_isBipartiteWith`.

Bipartiteness is supplied by the witnessed form `IsBipartiteWith s t`, since the statement must
name the side on which the degree is bounded. -/
theorem alon_krivelevich_sudakov_one_sided (r : ℕ) (hr : 1 ≤ r) (W : Type u) [Fintype W]
    (H : SimpleGraph W) (s t : Set W) (hb : H.IsBipartiteWith s t)
    (hdeg : ∀ v ∈ s, (H.neighborSet v).ncard ≤ r) :
    VinogradovLE (exR H) (scale r) := by
  sorry

/-- **What the known results DO settle, stated as the honest weakening.** For every bipartite
`r`-degenerate `H` there is SOME exponent strictly below `2` with `ex(n;H) ≪ n^α` — namely
`α = 2 - 1/(4r)`. This is what is proved; `Conjecture` asks for `α = 2 - 1/r`. -/
theorem exists_subquadratic_exponent (r : ℕ) (hr : 1 ≤ r) (W : Type u) [Fintype W]
    (H : SimpleGraph W) (hb : H.IsBipartite) (hd : IsDegenerate r H) :
    ∃ α : ℝ, α < 2 ∧ VinogradovLE (exR H) (fun n => (n : ℝ) ^ α) := by
  sorry

end Erdos146

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos146.ex_le_choose_two
#print axioms Erdos146.ex_zero
#print axioms Erdos146.bot_isDegenerate
#print axioms Erdos146.IsDegenerate.mono
#print axioms Erdos146.isContained_of_embedding
#print axioms Erdos146.isContained_of_le
#print axioms Erdos146.isDegenerate_of_isBipartiteWith
#print axioms Erdos146.conjecture_implies_r_two
#print axioms Erdos146.alon_krivelevich_sudakov
#print axioms Erdos146.alon_krivelevich_sudakov_one_sided
#print axioms Erdos146.exists_subquadratic_exponent
