/-
# A definitional bifurcation in "every K_4 / K_k receives a single colour"

Erdős problem #77 asks for the growth of the diagonal Ramsey number `R(k)`, defined through:

  SOURCE (frozen), verbatim:
  "a monochromatic copy of $K_k$"

Rendering "monochromatic" into a formal statement forces a choice that the English does not
make. Two readings are available, and they are NOT the same mathematics:

  READING A  (∃ c, ∀ edges)   there EXISTS one colour c such that EVERY edge of s has colour c
  READING B  (∀ edges, ∃ c)   for EVERY edge of s there EXISTS a colour c that it has

A is the intended notion. B is a theorem of the empty content: every edge has *some* colour, so
B holds for every colouring and every vertex set whatsoever.

⛔ THE CONSEQUENCE IS NOT COSMETIC. Under reading B the Ramsey property `Arrows n k` collapses to
"there is a k-element subset of `Fin n`", so the least such `n` is `k` itself. The diagonal
Ramsey number becomes `R(k) = k`, the growth question Erdős posed becomes trivial, and every
bound in the literature - `√2 ≤ liminf R(k)^(1/k)`, the improvements to `4 - 1/128` and
`3.7992...` - becomes false against the formal statement while remaining true of the mathematics.

This file exhibits the divergence in the kernel. Everything below is proved: no `sorry`, and
the axiom footprint is printed at the end so the reader need not take this file's word for it.

This is a statement about FORMALIZATION, not about Erdős and not about any cited author. No
human reader of the English is in any doubt which reading is meant. The point is that a machine
translating prose to Lean has no such intuition, the two renderings are separated by nothing but
the order of two quantifiers, and only one of them is the problem.
-/

-- @category research open
-- @AMS 5





import Mathlib
namespace Erdos77Bifurcation

/-- A 2-colouring of the edges of `K_n`, exactly as in the erdos-77 artifact. -/
abbrev Colouring (n : ℕ) := Sym2 (Fin n) → Bool

/-- READING A, the intended one: ONE colour serves every edge inside `s`. -/
def IsMonoCliqueA {n : ℕ} (C : Colouring n) (k : ℕ) (s : Finset (Fin n)) : Prop :=
  s.card = k ∧ ∃ c : Bool, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C (Sym2.mk x y) = c

/-- READING B, obtained from A by moving the existential inside the universals. -/
def IsMonoCliqueB {n : ℕ} (C : Colouring n) (k : ℕ) (s : Finset (Fin n)) : Prop :=
  s.card = k ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∃ c : Bool, C (Sym2.mk x y) = c

/-! ## B carries no information at all -/

/-- READING B IS VACUOUS. It holds for every colouring and every set of the right size, because
every edge trivially has the colour it has. The witness is `C (Sym2.mk x y)` itself. -/
theorem readingB_is_vacuous {n : ℕ} (C : Colouring n) (k : ℕ) (s : Finset (Fin n))
    (hcard : s.card = k) : IsMonoCliqueB C k s :=
  ⟨hcard, fun _ _ _ _ _ => ⟨_, rfl⟩⟩

/-! ## The two readings are inequivalent -/

/-- A concrete colouring on `Fin 3`: the edge `{0,1}` is `true`, every other edge is `false`.

⛔ The first version wrote `fun e => e = Sym2.mk 0 1`, which has type `Sym2 (Fin 3) → Prop`, not
`→ Bool`. Lean caught it as `failed to synthesize`. Recorded rather than quietly amended: a
colouring valued in `Prop` is not a 2-colouring, and the whole point of this file is that a
plausible-looking rendering can denote something other than the mathematics it names. -/
def C3 : Colouring 3 := fun e => decide (e = Sym2.mk (0 : Fin 3) (1 : Fin 3))

/-- THE DIVERGENCE, exhibited. On three vertices with the colouring `C3`, reading B holds and
reading A fails, so the two renderings denote different propositions and no argument about
intent can make them agree.

The failure of reading A here is decided by the kernel. Everything in sight is
finite - three vertices, two colours - so the statement is `Decidable` and no hand-rolled term
proof is needed. The first version of this file used explicit `Finset.mem_univ _` applications
and Lean rejected them with `Expected type must not contain metavariables`; that was a defect in
my proof script, not in the mathematics, and it is recorded rather than quietly amended. -/
theorem A_fails_on_C3 : ¬ IsMonoCliqueA C3 3 Finset.univ := by
  -- `IsMonoCliqueA` is an opaque `def`, so `decide` cannot see the finite structure through it
  -- and reports `failed to synthesize`. Unfolding first exposes the `Finset`/`Bool` quantifiers,
  -- all of which ARE decidable.
  unfold IsMonoCliqueA
  decide

theorem readings_inequivalent :
    ∃ (C : Colouring 3) (s : Finset (Fin 3)),
      IsMonoCliqueB C 3 s ∧ ¬ IsMonoCliqueA C 3 s :=
  ⟨C3, Finset.univ, readingB_is_vacuous _ _ _ (by decide), A_fails_on_C3⟩

/-! ## What the divergence does to the problem Erdős actually asked -/

/-- The Ramsey property under each reading. -/
def ArrowsA (n k : ℕ) : Prop := ∀ C : Colouring n, ∃ s : Finset (Fin n), IsMonoCliqueA C k s
def ArrowsB (n k : ℕ) : Prop := ∀ C : Colouring n, ∃ s : Finset (Fin n), IsMonoCliqueB C k s

/-- ⛔ UNDER READING B THE RAMSEY PROPERTY IS FREE the moment `Fin n` has `k` elements to choose.
So `ArrowsB n k` holds for every `n ≥ k`, the least such `n` is `k`, and `R(k) = k`. The growth
question - the entire content of Erdős problem 77 - disappears. -/
theorem arrowsB_trivial (n k : ℕ) (h : k ≤ n) : ArrowsB n k := by
  intro C
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (n := k) (by simpa using h)
  exact ⟨s, readingB_is_vacuous C k s hs⟩

/-- The same statement is FALSE for reading A at the smallest interesting case: three vertices do
not force a monochromatic triangle, so `ArrowsA 3 3` fails while `ArrowsB 3 3` holds. This is the
divergence at the level of the problem statement rather than the definition. -/
theorem arrowsA_not_trivial : ¬ ArrowsA 3 3 := by
  intro h
  obtain ⟨s, hcard, hmono⟩ := h C3
  have hs : s = Finset.univ := Finset.eq_univ_of_card s (by simpa using hcard)
  subst hs
  exact A_fails_on_C3 ⟨hcard, hmono⟩

/-- The two Ramsey properties are therefore inequivalent as well, not merely the definitions. -/
theorem arrows_readings_inequivalent : ArrowsB 3 3 ∧ ¬ ArrowsA 3 3 :=
  ⟨arrowsB_trivial 3 3 le_rfl, arrowsA_not_trivial⟩

end Erdos77Bifurcation

-- The reader should not have to trust this file. These are the axioms it rests on.
#print axioms Erdos77Bifurcation.readingB_is_vacuous
#print axioms Erdos77Bifurcation.A_fails_on_C3
#print axioms Erdos77Bifurcation.readings_inequivalent
#print axioms Erdos77Bifurcation.arrowsB_trivial
#print axioms Erdos77Bifurcation.arrowsA_not_trivial
#print axioms Erdos77Bifurcation.arrows_readings_inequivalent
