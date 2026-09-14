/-
# Erdős problem 601 — formalization of an OPEN problem ($500)

SOURCE (frozen, the only authority; both nodes of `entry-graph-erdos-601.json` read):

  question (n000-question), verbatim:
    "For which limit ordinals $\alpha$ is it true that if $G$ is a graph with vertex set
     $\alpha$ then $G$ must have either an infinite path or independent set on a set of
     vertices with order type $\alpha$?"

  resolution (n001-resolution), verbatim:
    "A problem of Erd\H{o}s, Hajnal, and Milner \cite{EHM70}, who proved this is true for
     $\alpha < \omega_1^{\omega+2}$. In \cite{Er82e} Erd\H{o}s offers \$250 for showing what
     happens when $\alpha=\omega_1^{\omega+2}$ and \$500 for settling the general case.
     Larson \cite{La90} proved this is true for all $\alpha<2^{\aleph_0}$ assuming Martin's
     axiom."

  references: [EHM70] Erdős, Hajnal and Milner, *Set mappings and polarized partition
              relations*, Combinatorial theory and its applications I-III (1970), 327-363.
              [Er82e] Erdős, *Some of my favourite problems which recently have been solved*.
              [La90] Larson.

STATUS: **OPEN**. Nothing below asserts which limit ordinals have the property. The per-ordinal
property is `HasProperty α`; the classification the source asks for is `Question`. The only
`sorry`-carrying theorems are the two results the resolution node attributes to named authors,
and each is named after its author.

--------------------------------------------------------------------------------
CONVENTIONS NAMED (every one of these the source leaves unstated)
--------------------------------------------------------------------------------

1. **VERTEX SET = `α.ToType`.** "a graph with vertex set $\alpha$" is read as a graph on
   Mathlib's canonical well-ordered type of order type `α`, i.e. `Ordinal.ToType α`, whose
   defining property is `Ordinal.type_toType : typeLT α.ToType = α`. Two things this buys:
   `α.ToType` already carries `LinearOrder` and `WellFoundedLT` instances, so both the graph
   and the order-type-of-a-subset operation are available without hand-built instances; and
   `HasProperty α` then quantifies over graphs on a type whose order type is *literally* `α`,
   not merely isomorphic to it.
   * THE ALTERNATIVE, and what it costs: `SimpleGraph ↥(Set.Iio α)` with `Set.Iio α : Set
     Ordinal.{u}`. That is the more literal reading of "vertex set $\alpha$" as the set of
     ordinals below `α`, but `Ordinal.type_lt_Iio` gives `typeLT (Iio o) = lift.{u+1} o` — a
     UNIVERSE LIFT. The equation `orderType S = α` would then have to be written `= lift α`,
     and every subsequent statement carries a `lift` that is pure bookkeeping. Rejected on
     that ground alone, not on faithfulness.
   * A third alternative, an abstract `[LinearOrder V] [WellFoundedLT V]` with hypothesis
     `typeLT V = α`, is *equivalent* but states the problem twice (once for `V`, once for the
     hypothesis) and makes the degenerate checks below harder to read. The general-`V` layer
     IS present here — `orderType` is stated for arbitrary such `V` — it is simply not what
     `HasProperty` quantifies over.

2. **ORDER TYPE OF A SET OF VERTICES.** `orderType S = typeLT ↥S` for `S : Set W`: the order
   type of the ORDER INDUCED on `S` by the ambient well-order. Mathlib supplies the
   `LinearOrder`/`WellFoundedLT` instances on the subtype `↥S`, and `Ordinal.type_set_le`
   /`Ordinal.type_mono` are stated in exactly this form, so this is Mathlib's own reading and
   not a local invention. `Subrel (· < ·) (· ∈ S)` is the same relation and is what
   `Ordinal.type_subrel` is phrased with; nothing here depends on which of the two spellings
   is used.

3. **"INFINITE PATH" = A ONE-WAY INFINITE RAY, WITH DISTINCT VERTICES.** `IsRay G p` for
   `p : ℕ → W` says exactly two things: `p` is INJECTIVE (the vertices are pairwise distinct —
   otherwise "path" would include a walk oscillating between two adjacent vertices, which
   every graph with a single edge contains, and the question would be trivial for every `α`),
   and `G.Adj (p n) (p (n+1))` for every `n` (consecutive vertices adjacent).
   * MATHLIB HAS NO INFINITE PATH. `SimpleGraph.Walk`, `.IsPath`, `.Path` are inductive on a
     FINITE vertex list; there is no `Ray`, no `SimpleGraph.End`, no infinite-walk type in
     `Mathlib/Combinatorics/SimpleGraph/`. The definition below is therefore local. This is
     reported as a genuine Mathlib gap, not a preference.
   * ONE-WAY, not two-way (`ℤ → W`). A two-way infinite path contains a one-way one, so the
     one-way reading is the WEAKER object to produce and hence the STRONGER form of the
     "must have" claim. Where the source's intent is ambiguous, the reading that makes the
     asserted statement stronger is the honest one to formalize; and in the Erdős–Hajnal–
     Milner setting "infinite path" is standard for a ray.
   * NO ORDER CONDITION IS IMPOSED ON THE RAY. `p` need not be increasing in the ordinal
     order, and its range need not have order type `ω`. It is a path in the GRAPH, and the
     ambient order plays no role in that branch.

4. **THE ORDER-TYPE CONDITION ATTACHES TO THE INDEPENDENT SET ONLY.** The source's phrase
   "either an infinite path or independent set on a set of vertices with order type $\alpha$"
   is grammatically ambiguous: "on a set of vertices with order type $\alpha$" could modify
   both disjuncts or only the second. It is read here as modifying ONLY the independent set.
   REASON, and it is decisive rather than stylistic: the resolution node records the property
   as PROVED for all `α < ω₁^(ω+2)`, a range containing ordinals of cardinality `ℵ₁`. A ray
   has at most `ℵ₀` vertices, so for uncountable `α` a path "on a set of vertices with order
   type `α`" cannot exist at all, and the both-disjuncts reading would make the EHM theorem
   false for every uncountable `α` in its own stated range. The other reading is recorded
   anyway as `HasPropertyBothConstrained`, asserted of nothing, so a reader can see precisely
   which statement is being taken and what the discarded one says.

5. **"LIMIT ORDINAL" = `Order.IsSuccLimit`.** Mathlib's `Ordinal.IsLimit` no longer exists; the
   current spelling is `Order.IsSuccLimit`, which on `Ordinal` means "neither `0` nor a
   successor" (`Ordinal.isSuccLimit_iff`). `0` is therefore NOT a limit ordinal here, which
   matters: `HasProperty 0` is vacuously TRUE (`ToType 0` is empty, so `Set.univ` is an
   independent set of order type `0`) and would otherwise pollute the classification with a
   degenerate member. See `hasProperty_zero` below, which is PROVED, and note that it is
   proved precisely so that its EXCLUSION by `IsSuccLimit` is visible rather than assumed.

6. **INDEPENDENT SET = `SimpleGraph.IsIndepSet`**, Mathlib's own `Set`-level predicate
   (`s.Pairwise fun v w => ¬G.Adj v w`). Note it is a PAIRWISE condition, so it imposes
   nothing on a vertex against itself; `SimpleGraph.Adj` is irreflexive anyway.

7. **"GRAPH" = `SimpleGraph`**: undirected, loopless, no multiple edges. The source says
   "graph" unqualified; in the Erdős partition-relation literature this is the standing
   meaning, and `IsIndepSet`/`Adj` are only sensible for it.

8. **"$2^{\aleph_0}$" AS A BOUND ON AN ORDINAL.** Larson's range "$\alpha<2^{\aleph_0}$"
   compares an ordinal to a cardinal; it is read as `α < Cardinal.continuum.ord`, i.e. `α`
   precedes the initial ordinal of the continuum. `Cardinal.lt_ord` makes this literally
   equivalent to `α.card < 𝔠` ("`α` has fewer than continuum many elements"), and that
   equivalence is PROVED below (`lt_continuum_iff_card_lt`) rather than assumed, so the two
   readings of the phrase are pinned as one.

9. **"$\omega_1^{\omega+2}$" IS ORDINAL EXPONENTIATION**, `ω₁ ^ (ω + 2)` with `ω₁ = ω_ 1`
   (`Ordinal.omega 1`, the first uncountable ordinal) and `ω = Ordinal.omega0`. Not cardinal
   exponentiation: the source's bound delimits a range of ORDINALS, and cardinal
   exponentiation of `ℵ₁` would not.

10. **MARTIN'S AXIOM IS NOT IN MATHLIB** (the only `martin*` in Mathlib is `Martingale`). It is
    therefore defined here, in the standard form: for every nonempty ccc partial order and
    every family of fewer than continuum many dense subsets, there is a filter meeting them
    all. Named sub-conventions: "ccc" = every antichain (pairwise incompatible set) is
    COUNTABLE; "dense" = downward dense (`∀ p, ∃ q ∈ D, q ≤ p`); "filter" = nonempty, upward
    closed, downward directed. The order convention is the set-theorist's, `q ≤ p` meaning
    "`q` is STRONGER than `p`". The definition is universe-polymorphic in the poset's universe
    and `larson_lt_continuum_of_martinsAxiom` uses it at the same universe as `α`.
    ⛔ This is a DEFINITION WRITTEN HERE, so that theorem is only as faithful as it is. It is
    flagged rather than hidden.

--------------------------------------------------------------------------------
DEGENERATE INSTANCES CHECKED (before anything was committed)
--------------------------------------------------------------------------------

* `α = 0` — NOT a limit ordinal under convention 5, but `HasProperty 0` is nevertheless TRUE
  and is proved below, so the reader can see that the `IsSuccLimit` guard is load-bearing.
* `α = ω`, the smallest limit ordinal — `omega0_lt_omega1_opow` below PROVES
  `ω < ω₁ ^ (ω + 2)`, i.e. the smallest limit ordinal lies strictly inside the range the
  resolution node attributes to Erdős–Hajnal–Milner. So neither settled theorem below is
  vacuous, and the open general case is genuinely about LARGE `α`. (This file does not assert
  `HasProperty ω`; that is EHM's theorem to give, and it is stated as theirs.)
* THE EMPTY GRAPH `⊥` — every set is independent, so `Set.univ` witnesses the second disjunct
  with order type exactly `α` (`bot_not_counterexample`, PROVED). If this had failed, the
  order-type convention 2 would have been wrong: it is the check that `orderType Set.univ` is
  `α` and not something smaller.
* THE COMPLETE GRAPH `⊤` — every injective `ℕ`-sequence is a ray, and for a limit `α` the
  vertex type is infinite, so the FIRST disjunct is witnessed (`top_not_counterexample`,
  PROVED). Together with the previous item this shows BOTH disjuncts are reachable, so
  `HasProperty` is not secretly a one-sided condition.
* ⛔ THE CLASSIFICATION QUESTION COLLAPSES AS A `Prop`, AND THIS IS PROVED
  (`question_is_provable_as_stated`). "For which `α` ...?" asks for an EXPLICIT description of
  a set; the bare existence of a correct answer set is a theorem of one line, since the
  extension `{α | HasProperty α}` is always such a set. `Question` is recorded because the
  source asks it, and its triviality is exhibited rather than glossed, so that no reader
  mistakes a proof of `Question` for the $500. THE MATHEMATICAL CONTENT IS IN `HasProperty α`
  FOR INDIVIDUAL `α`, and in `IsAnswer S` for an explicitly given `S`.

--------------------------------------------------------------------------------
MATHLIB USED / MATHLIB MISSING
--------------------------------------------------------------------------------
USED: `Ordinal.ToType` + `Ordinal.type_toType`; `Ordinal.type`/`typeLT`; `Ordinal.type_set_le`,
`Ordinal.type_mono`, `Ordinal.type_eq`; `Ordinal.omega0`, `Ordinal.omega` (`ω₁`);
`Order.IsSuccLimit` and `Ordinal.omega0_le_of_isSuccLimit`; `Cardinal.continuum`,
`Cardinal.ord`, `Cardinal.lt_ord`, `Cardinal.mk_toType`, `Cardinal.infinite_iff`;
`SimpleGraph`, `SimpleGraph.IsIndepSet`.
MISSING (and hence local): an infinite path / ray in a `SimpleGraph` (convention 3);
Martin's axiom, ccc, dense sets and filters on a poset (convention 10). `Ordinal.typein` was
NOT needed — `typein` names the order type of a strict initial segment, whereas this problem
needs the order type of an ARBITRARY subset, which is `type_set_le`'s `typeLT ↥S`.
-/
-- @category research open
-- @AMS 3
-- Category vocabulary and AMS tagging adopted from the formal-conjectures corpus
-- (509 files, measured 2026-08-28). Written as a comment rather than the corpus
-- attribute form, so this artifact still elaborates standalone, outside their project.






import Mathlib
open Ordinal Order

universe u v

namespace Erdos601

/-! ### Order types of sets of vertices (convention 2) -/

variable {W : Type*} [LinearOrder W] [WellFoundedLT W]

/-- The **order type of a set of vertices** `S`, in a well-ordered vertex type `W`: the order
type of the order `S` inherits from `W`. This is the reading of the source's "a set of
vertices with order type $\alpha$". -/
noncomputable def orderType (S : Set W) : Ordinal := typeLT ↥S

/-! ### The graph side (conventions 3, 6, 7) -/

/-- An **infinite path** (a one-way ray): a sequence of PAIRWISE DISTINCT vertices in which
consecutive vertices are adjacent.

Mathlib has no infinite path; `SimpleGraph.Walk`/`Path` are finite. Injectivity is what stops
this from being satisfied by every graph containing a single edge. -/
def IsRay (G : SimpleGraph W) (p : ℕ → W) : Prop :=
  Function.Injective p ∧ ∀ n : ℕ, G.Adj (p n) (p (n + 1))

/-- `G` **has an infinite path**. -/
def HasInfinitePath (G : SimpleGraph W) : Prop := ∃ p : ℕ → W, IsRay G p

/-! ### The property the source asks about -/

/-- **The per-ordinal property of Erdős problem 601.**

Source, verbatim: "if $G$ is a graph with vertex set $\alpha$ then $G$ must have either an
infinite path or independent set on a set of vertices with order type $\alpha$".

Vertex set is `α.ToType` (convention 1); the order-type condition constrains the independent
set only (convention 4). ⛔ This file asserts NOTHING about for which `α` this holds. -/
def HasProperty (α : Ordinal.{u}) : Prop :=
  ∀ G : SimpleGraph α.ToType,
    HasInfinitePath G ∨ ∃ S : Set α.ToType, G.IsIndepSet S ∧ orderType S = α

/-- The DISCARDED reading of convention 4, recorded so that the choice is visible: the
order-type condition constraining BOTH disjuncts, i.e. the ray's own range is required to have
order type `α`.

⛔ Asserted of nothing, and NO relation to `HasProperty` is claimed. For uncountable `α` the
first disjunct here is unsatisfiable, which is the reason this reading was not taken. -/
def HasPropertyBothConstrained (α : Ordinal.{u}) : Prop :=
  ∀ G : SimpleGraph α.ToType,
    (∃ p : ℕ → α.ToType, IsRay G p ∧ orderType (Set.range p) = α) ∨
      ∃ S : Set α.ToType, G.IsIndepSet S ∧ orderType S = α

/-- `S` is a **correct answer** to the source's question: the limit ordinals with the property
are exactly the members of `S`. Settling the problem means exhibiting such an `S` EXPLICITLY;
this file names no candidate. -/
def IsAnswer (S : Set Ordinal.{u}) : Prop :=
  ∀ α : Ordinal.{u}, IsSuccLimit α → (HasProperty α ↔ α ∈ S)

/-- **Erdős problem 601 ($500), the question as stated.**

Source, verbatim: "For which limit ordinals $\alpha$ is it true that if $G$ is a graph with
vertex set $\alpha$ then $G$ must have either an infinite path or independent set on a set of
vertices with order type $\alpha$?"

⛔ READ `question_is_provable_as_stated` BEFORE USING THIS. As a bare `Prop`, "for which `α`"
collapses: the extension of `HasProperty` is always a correct answer set, so `Question` is a
one-line theorem and is NOT the $500. The prize asks for an explicit `S` with `IsAnswer S`,
which is a demand on the FORM of `S` and is not expressible as a proposition. -/
def Question : Prop := ∃ S : Set Ordinal.{u}, IsAnswer S

/-! ### Martin's axiom, defined here because Mathlib has none (convention 10) -/

/-- Two conditions are **compatible** if some condition is stronger than both. -/
def Compat {P : Type*} [Preorder P] (p q : P) : Prop := ∃ r : P, r ≤ p ∧ r ≤ q

/-- `P` **has the countable chain condition**: every pairwise-incompatible set is countable. -/
def IsCcc (P : Type*) [Preorder P] : Prop :=
  ∀ A : Set P, (∀ p ∈ A, ∀ q ∈ A, p ≠ q → ¬ Compat p q) → A.Countable

/-- `D` is **dense**: every condition has a stronger condition in `D`. -/
def IsDenseBelow {P : Type*} [Preorder P] (D : Set P) : Prop := ∀ p : P, ∃ q ∈ D, q ≤ p

/-- `G` is a **filter**: nonempty, upward closed, downward directed. -/
def IsUpFilter {P : Type*} [Preorder P] (G : Set P) : Prop :=
  G.Nonempty ∧ (∀ p ∈ G, ∀ q : P, p ≤ q → q ∈ G) ∧
    (∀ p ∈ G, ∀ q ∈ G, ∃ r ∈ G, r ≤ p ∧ r ≤ q)

/-- **Martin's axiom** `MA`: for every nonempty ccc partial order `P` and every family `𝒟` of
fewer than $2^{\aleph_0}$ many dense subsets of `P`, some filter on `P` meets every member of
`𝒟`. ⛔ Local definition; Mathlib has no Martin's axiom. -/
def MartinsAxiom : Prop :=
  ∀ (P : Type v) (_ : PartialOrder P), Nonempty P → IsCcc P →
    ∀ 𝒟 : Set (Set P), Cardinal.mk ↥𝒟 < Cardinal.continuum.{v} →
      (∀ D ∈ 𝒟, IsDenseBelow D) →
        ∃ G : Set P, IsUpFilter G ∧ ∀ D ∈ 𝒟, (G ∩ D).Nonempty

/-! ### What the resolution node records as settled, each named after its author -/

/-- **Erdős–Hajnal–Milner** [EHM70].

Source, verbatim: "A problem of Erd\H{o}s, Hajnal, and Milner \cite{EHM70}, who proved this is
true for $\alpha < \omega_1^{\omega+2}$."

A published theorem, not one of the open cases; the proof is `sorry` here. The bound is
ordinal exponentiation (convention 9). ⛔ The case $\alpha=\omega_1^{\omega+2}$ itself is
exactly what Erdős offered \$250 for and is NOT covered by this statement. -/
theorem erdos_hajnal_milner_lt_omega1_opow_omega_add_two
    (α : Ordinal.{u}) (hα : IsSuccLimit α) (hbound : α < ω₁ ^ (Ordinal.omega0 + 2)) :
    HasProperty α := by
  sorry

/-- **Larson** [La90].

Source, verbatim: "Larson \cite{La90} proved this is true for all $\alpha<2^{\aleph_0}$
assuming Martin's axiom."

A published theorem, conditional on Martin's axiom, whose statement is the LOCAL definition
`MartinsAxiom` above (convention 10); the bound is read via `Cardinal.ord` (convention 8). The
proof is `sorry` here. -/
theorem larson_lt_continuum_of_martinsAxiom
    (hMA : MartinsAxiom.{u}) (α : Ordinal.{u}) (hα : IsSuccLimit α)
    (hbound : α < Cardinal.continuum.{u}.ord) :
    HasProperty α := by
  sorry

/-! ### Anti-vacuity controls (PROVED, no `sorry`, kernel-checked)

A `sorry`-carrying statement elaborates whether or not its definitions say anything. Everything
below is fully proved, mentions only this file's own definitions, and is cheap machine-checked
evidence that those definitions bite. -/

/-- **Convention 2 is sound, upper bound.** The order type of a set of vertices never exceeds
the order type of the whole vertex set. -/
-- @category test
theorem orderType_le_type (S : Set W) : orderType S ≤ typeLT W := Ordinal.type_set_le S

/-- **Convention 2 is sound, monotone.** A larger set of vertices has at least as large an
order type. -/
-- @category test
theorem orderType_mono {S T : Set W} (h : S ⊆ T) : orderType S ≤ orderType T :=
  Ordinal.type_mono h

/-- The empty set of vertices has order type `0`. The degenerate end of convention 2. -/
-- @category test
theorem orderType_empty : orderType (∅ : Set W) = 0 := by
  simp [orderType]

/-- **The load-bearing check on convention 2.** ALL the vertices have the order type of the
whole vertex type. Without this, `orderType Set.univ` could be some smaller ordinal and the
second disjunct of `HasProperty` would be unsatisfiable for trivial reasons. -/
-- @category test
theorem orderType_univ : orderType (Set.univ : Set W) = typeLT W :=
  Ordinal.type_eq.2 ⟨⟨Equiv.Set.univ W, Iff.rfl⟩⟩

/-- **Conventions 1 and 2 agree.** On the vertex type `α.ToType`, all the vertices have order
type exactly `α` — this is where `Ordinal.type_toType` earns convention 1. -/
-- @category test
theorem orderType_univ_toType (α : Ordinal.{u}) :
    orderType (Set.univ : Set α.ToType) = α := by
  rw [orderType_univ, Ordinal.type_toType]

/-- Every set of vertices of `α.ToType` has order type at most `α`, so the equation
`orderType S = α` in `HasProperty` is asking for a MAXIMAL set, not an impossible one. -/
-- @category test
theorem orderType_le_self (α : Ordinal.{u}) (S : Set α.ToType) : orderType S ≤ α := by
  have h := Ordinal.type_set_le S
  rw [Ordinal.type_toType] at h
  exact h

-- @category test
omit [LinearOrder W] [WellFoundedLT W] in
/-- **Convention 3 bites.** The vertices of an infinite path really are infinitely many; this
is what injectivity was put there for. -/
theorem infinite_range_of_isRay (G : SimpleGraph W) (p : ℕ → W) (h : IsRay G p) :
    (Set.range p).Infinite :=
  Set.infinite_range_of_injective h.1

/-- **DEGENERATE CASE: the empty graph is not a counterexample, for any `α`.** Every set is
independent in `⊥`, and `Set.univ` has order type `α`, so the second disjunct holds. -/
-- @category test
theorem bot_not_counterexample (α : Ordinal.{u}) :
    HasInfinitePath (⊥ : SimpleGraph α.ToType) ∨
      ∃ S : Set α.ToType, (⊥ : SimpleGraph α.ToType).IsIndepSet S ∧ orderType S = α := by
  refine Or.inr ⟨Set.univ, ?_, orderType_univ_toType α⟩
  intro a _ b _ _
  simp

/-- **DEGENERATE CASE: `α = 0`.** `HasProperty 0` holds, vacuously — `ToType 0` is empty. This
is why convention 5's `IsSuccLimit` guard is load-bearing: without it the classification would
contain `0` for reasons having nothing to do with the mathematics. -/
-- @category test
theorem hasProperty_zero : HasProperty 0 := by
  intro G
  refine Or.inr ⟨Set.univ, ?_, orderType_univ_toType 0⟩
  intro a _ _ _ _
  exact (IsEmpty.false a).elim

/-- **DEGENERATE CASE: the complete graph is not a counterexample on a limit `α`.** For a limit
ordinal the vertex type is infinite, so any injection from `ℕ` is a ray in `⊤`. Together with
`bot_not_counterexample` this shows BOTH disjuncts of `HasProperty` are reachable. -/
-- @category test
theorem top_not_counterexample (α : Ordinal.{u}) (hα : IsSuccLimit α) :
    HasInfinitePath (⊤ : SimpleGraph α.ToType) := by
  have hle : Ordinal.omega0 ≤ α := Ordinal.omega0_le_of_isSuccLimit hα
  have hcard : Cardinal.aleph0 ≤ Cardinal.mk α.ToType := by
    rw [Cardinal.mk_toType]
    simpa using Ordinal.card_le_card hle
  have hinf : Infinite α.ToType := Cardinal.infinite_iff.2 hcard
  refine ⟨Infinite.natEmbedding α.ToType,
    (Infinite.natEmbedding α.ToType).injective, ?_⟩
  intro n
  simp only [SimpleGraph.top_adj, ne_eq]
  exact fun h => absurd ((Infinite.natEmbedding α.ToType).injective h) (by omega)

/-- **DEGENERATE CASE: `α = ω`, the smallest limit ordinal, lies strictly inside the
Erdős–Hajnal–Milner range.** So neither settled theorem above is vacuous at the bottom, and the
open part of the problem is genuinely about large `α`.

⛔ This is a statement about ORDINAL ARITHMETIC only. It does not assert `HasProperty ω`. -/
-- @category test
theorem omega0_lt_omega1_opow : Ordinal.omega0 < ω₁ ^ (Ordinal.omega0 + 2) := by
  calc Ordinal.omega0 < ω₁ := Ordinal.omega0_lt_omega_one
    _ = ω₁ ^ (1 : Ordinal) := (Ordinal.opow_one _).symm
    _ ≤ ω₁ ^ (Ordinal.omega0 + 2) := by
        refine Ordinal.opow_le_opow_right ?_ ?_
        · exact lt_of_lt_of_le Ordinal.omega0_pos Ordinal.omega0_lt_omega_one.le
        · exact le_trans one_le_two le_add_self

/-- **Convention 8 pinned.** The two readings of Larson's bound "$\alpha<2^{\aleph_0}$" — `α`
precedes the initial ordinal of the continuum, and `α` has fewer than continuum many elements —
are the same statement. -/
-- @category test
theorem lt_continuum_iff_card_lt (α : Ordinal.{u}) :
    α < Cardinal.continuum.{u}.ord ↔ α.card < Cardinal.continuum.{u} :=
  Cardinal.lt_ord

/-- ⛔ **THE CLASSIFICATION QUESTION COLLAPSES AS A `Prop`, AND HERE IS THE ONE-LINE PROOF.**

`Question` says only that SOME set is a correct answer, and the extension of `HasProperty` is
always one. This theorem is in the file so that nobody mistakes a proof of `Question` for a
solution of Erdős problem 601: the prize asks for an EXPLICIT `S` with `IsAnswer S`, a demand
on the form of `S` that no `Prop` can carry. The mathematical content lives in `HasProperty α`
for individual `α`, and in `IsAnswer S` for an `S` given by name. -/
-- @category test
theorem question_is_provable_as_stated : Question.{u} :=
  ⟨{α | HasProperty α}, fun _ _ => Iff.rfl⟩

/-- Whatever the answer set is, it is unique on limit ordinals: two correct answers agree
there. A cheap check that `IsAnswer` is the right shape for "the set of limit ordinals with the
property", rather than a condition many unrelated sets could satisfy. -/
-- @category test
theorem isAnswer_agree {S T : Set Ordinal.{u}} (hS : IsAnswer S) (hT : IsAnswer T)
    (α : Ordinal.{u}) (hα : IsSuccLimit α) : α ∈ S ↔ α ∈ T :=
  (hS α hα).symm.trans (hT α hα)

end Erdos601

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos601.erdos_hajnal_milner_lt_omega1_opow_omega_add_two
#print axioms Erdos601.larson_lt_continuum_of_martinsAxiom
#print axioms Erdos601.orderType_le_type
#print axioms Erdos601.orderType_mono
#print axioms Erdos601.orderType_empty
#print axioms Erdos601.orderType_univ
#print axioms Erdos601.orderType_univ_toType
#print axioms Erdos601.orderType_le_self
#print axioms Erdos601.infinite_range_of_isRay
#print axioms Erdos601.bot_not_counterexample
#print axioms Erdos601.hasProperty_zero
#print axioms Erdos601.top_not_counterexample
#print axioms Erdos601.omega0_lt_omega1_opow
#print axioms Erdos601.lt_continuum_iff_card_lt
#print axioms Erdos601.question_is_provable_as_stated
#print axioms Erdos601.isAnswer_agree
