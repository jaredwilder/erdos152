/- 
SOURCE (frozen), NODE n000-question (question), VERBATIM:
For any fixed $s\geq 3$,\[R(s,k) \gg \frac{k^{s-1}}{(\log k)^c}\]for some constant $c=c(s)>0$.
-/

/-
SOURCE (frozen), NODE n001-resolution (resolution), VERBATIM:
#986 : [Er90b,p.18] graph theory | ramsey theory According to Chung and Graham [ChGr98] this was first conjectured by Erdős in 1947. Spencer [Sp77] proved this for $s=3$ and Mattheus and Verstraete [MaVe23] proved this for $s=4$. The best general bounds available for $s\geq 5$ are\[\frac{k^{s-1}}{(\log k)^{2s-4}}\ll_k R(s,k) \ll_s \frac{k^{s-1}}{(\log k)^{s-2}}.\]The lower bound was proved by Bradač [Br26] , in particular resolving this problem. (An earlier version of Bradač's work had an exponnt of $s-2$ - the adjustment to achieve $s-1$ was observed by an internal model at OpenAI.) This improved an earlier lower bound due to Bohman and Keevash [BoKe10] . The upper bound was proved by Ajtai, Komlós, and Szemerédi [AKS80] . Li, Rousseau, and Zang [LRZ01] have shown that $\ll_s$ in the upper bound can be improved to $\leq (1+o(1))$. The special case $s=3$ is the topic of [165] and $s=4$ is the topic of [166] . This problem is #6 in Ramsey Theory in the graphs problem collection. See also [920] . (The reference [Er90b] only refers to the cases $s=3$ and $s=4$ of this problem. The best reference I have that Erdős made the general conjecture is [ChGr98] .) Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (6) Proof claims (0) More information and links This page was last edited 21 June 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #986, https://www.erdosproblems.com/986, accessed 2026-08-30 From the external database . You can help update this.) Formalised statement? No ( create one ) OEIS A000791 , A059442 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None
-/





import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos986

/-- A two-element subset of the vertex set `Fin n`, representing an edge. -/
def Edge (n : ℕ) := {p : Finset (Fin n) // p.card = 2}

/-- A red-blue edge-colouring of the complete graph on `Fin n`. -/
def Coloring (n : ℕ) := Edge n → Bool

/-- `Mono c t b` says that the colouring `c` has a monochromatic `t`-vertex
set whose every edge has colour `b`. -/
def Mono {n : ℕ} (c : Coloring n) (t : ℕ) (b : Bool) : Prop :=
  ∃ A : Finset (Fin n), A.card = t ∧
    ∀ p : Edge n, p.1 ⊆ A → c p = b

/-- The finite Ramsey property: every red-blue colouring of `K_n` contains
either a red `s`-clique or a blue `k`-clique. -/
def RamseyProperty (s k n : ℕ) : Prop :=
  ∀ c : Coloring n, Mono c s true ∨ Mono c k false

/-- A bounded, decidable finite version of the Ramsey predicate, obtained by
restricting the parameters to the first `N` values. -/
def RamseyPropertyFinite (s k N : ℕ) : Prop :=
  ∀ n ≤ N, RamseyProperty s k n

/-- The Ramsey number, defined as the infimum of the set of orders having the
finite Ramsey property. Since `sInf` returns junk on an empty set, all uses of
this definition must provide nonemptiness; the lower-bound application below
is safe from vacuity because the relevant Ramsey sets are required to be
nonempty. -/
noncomputable def RamseyNumber (s k : ℕ) : ℕ :=
  sInf {n : ℕ | RamseyProperty s k n}

/-- The constant all-red colouring on `K₃`. -/
def allRed : Coloring 3 :=
  fun _ => true

/-- POSITIVE WITNESS: an all-red triangle contains a monochromatic
three-vertex set. -/
theorem mono_witness_pos : Mono allRed 3 true := by
  decide

/-- NEGATIVE WITNESS: the same all-red triangle has no monochromatic
two-vertex set of the opposite colour; this is a one-colour near miss. -/
theorem mono_witness_neg : ¬ Mono allRed 2 false := by
  decide

/-- POSITIVE WITNESS: every colouring of `K₃` has either a red triangle or a
blue edge. -/
theorem ramsey_property_witness_pos : RamseyProperty 3 2 3 := by
  decide

/-- NEGATIVE WITNESS: `K₂` is the near-miss order for the preceding finite
Ramsey assertion. -/
theorem ramsey_property_witness_neg : ¬ RamseyProperty 3 2 2 := by
  decide

/-- POSITIVE WITNESS: the bounded finite predicate holds through order `3`
for the parameters `(s,k) = (3,2)`. -/
theorem ramsey_property_finite_witness_pos :
    RamseyPropertyFinite 3 2 3 := by
  decide

/-- NEGATIVE WITNESS: extending the preceding bounded assertion by the
single near-miss order `4` still exposes the failed order `2`. -/
theorem ramsey_property_finite_witness_neg :
    ¬ RamseyPropertyFinite 3 2 4 := by
  decide

/-- The defining set for `RamseyNumber 3 2` is nonempty, so its `sInf` is not
being used at the empty-set junk value. -/
theorem ramsey_set_nonempty_3_2 :
    ({n : ℕ | RamseyProperty 3 2 n}).Nonempty := by
  exact ⟨3, ramsey_property_witness_pos⟩

/-- The source's resolved asymptotic lower bound, read in the standard
eventual real-valued sense: for every fixed `s ≥ 3`, there are positive
constants `c` and `C` and a threshold `K` such that
`C * k^(s-1) / (log k)^c ≤ R(s,k)` for all `k ≥ K`.
The source clause is “For any fixed $s\geq 3$, ... for some constant
$c=c(s)>0$”; the theorem below preserves that quantifier order. The use of
`RamseyNumber` involves `sInf`, whose junk value on an empty set would make a
lower bound unsafe, so the required nonemptiness of every defining Ramsey set
is included as an explicit hypothesis. -/
theorem ramsey_asymptotic_lower_bound :
    ∀ s : ℕ, 3 ≤ s →
      (∀ k : ℕ, ({n : ℕ | RamseyProperty s k n}).Nonempty) →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
          C * (k : ℝ) ^ (s - 1) /
              Real.rpow (Real.log (k : ℝ)) c ≤
            (RamseyNumber s k : ℝ) := by
  sorry Erdos986
