/-
Erdős problem #136 — edge colourings of K_n in which every K_4 gets at least 5 colours.

SOURCE (frozen), question node `n000-question`:
  "Let $f(n)$ be the smallest number of colours required to colour the edges of $K_n$ such
   that every $K_4$ contains at least 5 colours. Determine the size of $f(n)$."

SOURCE (frozen), resolution node `n001-resolution`:
  "Asked by Erdős and Gyárfás, who proved that \[\frac{5}{6}(n-1) < f(n)<n,\] and that
   $f(9)=8$. Erdős believed the upper bound is closer to the truth. In fact the lower bound
   is: Bennett, Cushman, Dudek, and Pralat [BCDP22] have shown that \[f(n) \sim \frac{5}{6}n.\]
   Joos and Mubayi [JoMu22] have found a shorter proof of this. See also [135]."

CONVENTIONS NAMED (the source leaves these unstated):

1. "every K_4 contains at least 5 colours" is read as: for every 4-element set S of vertices,
   the SIX edges inside S carry at least 5 distinct colours (i.e. the image of the colouring
   restricted to the 6 edges of S has cardinality ≥ 5).  This is the only reading that makes
   the constant 5 meaningful (6 edges, so "≥ 5" is "at most one repeated colour class").

2. A colouring of K_n with k colours is modelled as a SYMMETRIC function
   `c : Fin n → Fin n → Fin k`.  Symmetry is imposed explicitly; without it the image over
   `Finset.offDiag` would count the two orientations of an edge as two colours and would
   INFLATE the count, i.e. would weaken the constraint.  Diagonal entries `c i i` are
   irrelevant: `Finset.offDiag` excludes them.

3. `f n` is defined for ALL n, as `sInf` over k of "k colours suffice".  For n < 4 the
   constraint is vacuous, so f 0 = 0 and f 1 = f 2 = f 3 = 1; the asymptotic statement is
   unaffected.  The set is nonempty for every n (a rainbow colouring works), so the `sInf`
   is a genuine minimum and not the junk value 0.

4. "f(n) ~ 5n/6" is read as the RATIO TENDING TO ONE (`f n / (5n/6) → 1`), which is the
   literal meaning of `~`, and is strictly stronger than any big-O / big-Θ statement.
-/

-- @category research solved
-- @AMS 5
-- Category vocabulary and AMS tagging adopted from the
-- formal-conjectures corpus (509 files, measured 2026-08-28). Written as a comment
-- rather than the corpus attribute form, so this artifact still elaborates
-- standalone, outside their project.









import Mathlib
open Filter Topology

namespace Erdos136

/-- The number of distinct colours appearing on the edges spanned by the vertex set `S`. -/
def colourCount {n k : ℕ} (c : Fin n → Fin n → Fin k) (S : Finset (Fin n)) : ℕ :=
  (S.offDiag.image fun p => c p.1 p.2).card

/-- `c` is a symmetric edge colouring of `K n` with `k` colours in which every `K 4`
receives at least `5` distinct colours. -/
def IsGoodColouring (n k : ℕ) (c : Fin n → Fin n → Fin k) : Prop :=
  (∀ i j, c i j = c j i) ∧
    ∀ S : Finset (Fin n), S.card = 4 → 5 ≤ colourCount c S

/-- `f n` : the least number of colours needed to colour the edges of `K n` so that every
`K 4` receives at least 5 colours. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ c : Fin n → Fin n → Fin k, IsGoodColouring n k c}

/-! ### Anti-vacuity controls (PROVED, not part of the source)

A `sorry`-carrying statement elaborates whether or not its definitions say anything. The
declarations in this section are fully proved and exercise this file's own `colourCount`,
`IsGoodColouring` and `f`. They also discharge `f_spec`, which convention 3 above asserts and
which the `sInf` in the definition of `f` silently depends on: without it `f n` could be the
junk value `0` rather than a genuine minimum. -/

/-- The symmetric **rainbow** colouring of `K n`: the edge `{i, j}` receives the colour that
the Mathlib equivalence `Fin n × Fin n ≃ Fin (n * n)` assigns to `(min i j, max i j)`.
Distinct edges therefore receive distinct colours. -/
def rainbow (n : ℕ) (i j : Fin n) : Fin (n * n) :=
  finProdFinEquiv (min i j, max i j)

/-- The rainbow colouring is symmetric, as convention 2 requires of any colouring. -/
-- @category test
theorem rainbow_comm {n : ℕ} (i j : Fin n) : rainbow n i j = rainbow n j i := by
  rw [rainbow, rainbow, min_comm, max_comm]

/-- Each rainbow colour is used by at most the two orientations of a single edge. This is the
injectivity fact that makes the rainbow colouring rainbow. -/
-- @category test
theorem rainbow_fiber_le_two {n : ℕ} (S : Finset (Fin n)) (b : Fin (n * n)) :
    (S.offDiag.filter (fun p : Fin n × Fin n => rainbow n p.1 p.2 = b)).card ≤ 2 := by
  rcases Finset.eq_empty_or_nonempty
      (S.offDiag.filter (fun p : Fin n × Fin n => rainbow n p.1 p.2 = b)) with h | ⟨p, hp⟩
  · simp [h]
  · have hsub : S.offDiag.filter (fun p : Fin n × Fin n => rainbow n p.1 p.2 = b)
        ⊆ ({p, (p.2, p.1)} : Finset (Fin n × Fin n)) := by
      intro q hq
      have hq' : rainbow n q.1 q.2 = b := (Finset.mem_filter.mp hq).2
      have hp' : rainbow n p.1 p.2 = b := (Finset.mem_filter.mp hp).2
      simp only [rainbow] at hq' hp'
      have hmm : (min q.1 q.2, max q.1 q.2) = (min p.1 p.2, max p.1 p.2) :=
        finProdFinEquiv.injective (hq'.trans hp'.symm)
      have h1 : min q.1 q.2 = min p.1 p.2 := congrArg Prod.fst hmm
      have h2 : max q.1 q.2 = max p.1 p.2 := congrArg Prod.snd hmm
      have hcases : (q.1 = p.1 ∧ q.2 = p.2) ∨ (q.1 = p.2 ∧ q.2 = p.1) := by
        rcases le_total q.1 q.2 with hq2 | hq2 <;> rcases le_total p.1 p.2 with hp2 | hp2
        · rw [min_eq_left hq2, min_eq_left hp2] at h1
          rw [max_eq_right hq2, max_eq_right hp2] at h2
          exact Or.inl ⟨h1, h2⟩
        · rw [min_eq_left hq2, min_eq_right hp2] at h1
          rw [max_eq_right hq2, max_eq_left hp2] at h2
          exact Or.inr ⟨h1, h2⟩
        · rw [min_eq_right hq2, min_eq_left hp2] at h1
          rw [max_eq_left hq2, max_eq_right hp2] at h2
          exact Or.inr ⟨h2, h1⟩
        · rw [min_eq_right hq2, min_eq_right hp2] at h1
          rw [max_eq_left hq2, max_eq_left hp2] at h2
          exact Or.inl ⟨h2, h1⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl (Prod.ext_iff.mpr ⟨e1, e2⟩)
      · exact Or.inr (Prod.ext_iff.mpr ⟨e1, e2⟩)
    calc (S.offDiag.filter (fun p : Fin n × Fin n => rainbow n p.1 p.2 = b)).card
        ≤ ({p, (p.2, p.1)} : Finset (Fin n × Fin n)).card := Finset.card_le_card hsub
      _ ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)

/-- A `4`-set spans `12` ordered off-diagonal pairs, and the rainbow colouring uses each
colour at most twice, so it shows at least `6 ≥ 5` colours on every `K 4`. -/
-- @category test
theorem five_le_colourCount_rainbow {n : ℕ} (S : Finset (Fin n)) (hS : S.card = 4) :
    5 ≤ colourCount (rainbow n) S := by
  have hmul := Finset.card_le_mul_card_image (f := fun p : Fin n × Fin n => rainbow n p.1 p.2)
    S.offDiag 2 (fun b _ => rainbow_fiber_le_two S b)
  have hod : S.offDiag.card = 12 := by rw [Finset.offDiag_card, hS]
  show 5 ≤ (S.offDiag.image fun p : Fin n × Fin n => rainbow n p.1 p.2).card
  omega

/-- The rainbow colouring is a good colouring, for every `n`. -/
-- @category test
theorem isGoodColouring_rainbow (n : ℕ) : IsGoodColouring n (n * n) (rainbow n) :=
  ⟨fun i j => rainbow_comm i j, fun S hS => five_le_colourCount_rainbow S hS⟩

/-- The `K 4` constraint is VACUOUS below `n = 4` (convention 3): there is no `4`-element
subset of `Fin n` at all, so every symmetric colouring is good. -/
-- @category test
theorem isGoodColouring_of_lt_four {n k : ℕ} (hn : n < 4) (c : Fin n → Fin n → Fin k)
    (hsymm : ∀ i j, c i j = c j i) : IsGoodColouring n k c := by
  refine ⟨hsymm, fun S hS => ?_⟩
  have hle : S.card ≤ n := by simpa using S.card_le_univ
  omega

/-- Sanity lemma (not part of the source): the defining set is nonempty for every `n`, so
`f n` really is a minimum. -/
-- @category test
theorem f_spec (n : ℕ) :
    {k : ℕ | ∃ c : Fin n → Fin n → Fin k, IsGoodColouring n k c}.Nonempty :=
  ⟨n * n, rainbow n, isGoodColouring_rainbow n⟩

/-- Consequence of `f_spec` (and of the vacuity lemma): `f 0 = 0`, exactly the value convention
3 records. Read together with `f_spec` this shows the `sInf` is attained rather than junk. -/
-- @category test
theorem f_zero : f 0 = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl ⟨fun i _ => i.elim0, isGoodColouring_of_lt_four (by norm_num) _
    (fun i _ => i.elim0)⟩)

/-! ### MAIN THEOREM — the resolution of Erdős #136

Bennett, Cushman, Dudek and Pralat: `f n ~ (5/6) n`, i.e. the ratio tends to 1. -/

theorem erdos_136_asymptotic :
    Tendsto (fun n : ℕ => (f n : ℝ) / (5 * (n : ℝ) / 6)) atTop (𝓝 1) := by
  sorry

/-! ### Equivalent restatement of the MAIN theorem (same content, different normalisation) -/

theorem erdos_136_asymptotic' :
    Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)) atTop (𝓝 (5 / 6)) := by
  sorry

/-! ### SEPARATE, EARLIER result of Erdős and Gyárfás (NOT part of the main theorem)

The source states `(5/6)(n-1) < f(n) < n` with no range.  Read literally over all `n` the
statement is FALSE: `f 4 = 5` and `f 5 = 5`, so `f n < n` fails at `n = 4, 5`.  We therefore
state it in the "for all sufficiently large n" form.  This is an explicit WEAKENING of the
unrestricted reading, chosen because the unrestricted reading is refutable. -/

theorem erdos_gyarfas_bounds :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      5 / 6 * ((n : ℝ) - 1) < (f n : ℝ) ∧ (f n : ℝ) < (n : ℝ) := by
  sorry

/-! ### SEPARATE, exact small value of Erdős and Gyárfás (NOT part of the main theorem) -/

theorem erdos_gyarfas_f_nine : f 9 = 8 := by
  sorry

end Erdos136

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos136.rainbow_comm
#print axioms Erdos136.rainbow_fiber_le_two
#print axioms Erdos136.five_le_colourCount_rainbow
#print axioms Erdos136.isGoodColouring_rainbow
#print axioms Erdos136.isGoodColouring_of_lt_four
#print axioms Erdos136.f_spec
#print axioms Erdos136.f_zero
#print axioms Erdos136.erdos_136_asymptotic
#print axioms Erdos136.erdos_136_asymptotic'
#print axioms Erdos136.erdos_gyarfas_bounds
#print axioms Erdos136.erdos_gyarfas_f_nine
