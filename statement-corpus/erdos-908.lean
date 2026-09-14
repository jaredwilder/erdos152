/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f:\mathbb{R}\to \mathbb{R}$ be such that $f(x+h)-f(x)$ is measurable for every $h>0$. Is it true that\[f=g+h+r\]where $g$ is continuous, $h$ is additive (so $h(x+y)=h(x)+h(y)$), and $r(x+h)-r(x)=0$ for every $h$ and almost all (depending on $h$) $x$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#908 : [Er81b,p.31] [Er82e] analysis A conjecture of de Bruijn and Erdős. Answered in the affirmative by Laczkovich [La80] . See also [907] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 30 December 2025. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #908, https://www.erdosproblems.com/908, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable Working on formalising mdelvecchio Previous Next
-/




import Mathlib
open Classical
open Filter
open scoped Topology

-- @category research solved








open Classical Filter

namespace Erdos908

/-- The additive-function condition appearing in the source: `AdditiveFunction a`
means that `a (x + y) = a x + a y` for all real `x` and `y`. -/
def AdditiveFunction (a : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, a (x + y) = a x + a y

/-- POSITIVE WITNESS: the identity map is additive. -/
theorem additiveFunction_witness_pos :
    AdditiveFunction (fun x : ℝ => x) := by
  intro x y
  rfl

/-- NEGATIVE WITNESS: the constant-one map is a near miss, failing only the
additivity equation at the pair `(0, 0)`. -/
theorem additiveFunction_witness_neg :
    ¬ AdditiveFunction (fun _ : ℝ => (1 : ℝ)) := by
  intro h
  have h' := h 0 0
  norm_num at h'

/-- A finite, decidable bounded version of additivity on the first `n`
nonnegative integer inputs. -/
def AdditiveFunctionFinite (n : ℕ) (a : Fin n → ℤ) : Prop :=
  ∀ x y : Fin n, x.1 + y.1 < n →
    a ⟨x.1 + y.1, ‹x.1 + y.1 < n›⟩ = a x + a y

/-- POSITIVE WITNESS: the coordinate map is additive on the finite test
domain with three inputs. -/
theorem additiveFunctionFinite_witness_pos :
    AdditiveFunctionFinite 3 (fun x : Fin 3 => (x.1 : ℤ)) := by
  intro x y hxy
  simp
  omega

/-- NEGATIVE WITNESS: changing the value at the input `2` gives a near miss
to the preceding finite additive function. -/
theorem additiveFunctionFinite_witness_neg :
    ¬ AdditiveFunctionFinite 3
      (fun x : Fin 3 => if x.1 = 2 then (0 : ℤ) else (x.1 : ℤ)) := by
  intro h
  have h' := h ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide)
  norm_num at h'

/-- The almost-everywhere translation-invariance condition for the residual
term.  Thus `TranslationInvariantAe r` means that for each positive
translation `h`, the equality `r (x+h) = r x` holds for almost every `x`
with respect to Lebesgue measure. -/
def TranslationInvariantAe (r : ℝ → ℝ) : Prop :=
  ∀ h : ℝ, 0 < h → ∀ᵐ x ∂volume, r (x + h) = r x

/-- POSITIVE WITNESS: the zero function is invariant under every translation. -/
theorem translationInvariantAe_witness_pos :
    TranslationInvariantAe (fun _ : ℝ => (0 : ℝ)) := by
  intro h hh
  filter_upwards [] with x
  rfl

/-- NEGATIVE WITNESS: the identity map is a near miss, and already fails
translation invariance for the single positive translation `1`. -/
theorem translationInvariantAe_witness_neg :
    ¬ TranslationInvariantAe (fun x : ℝ => x) := by
  intro h
  have h' := h 1 (by norm_num)
  have h'' : ∀ᵐ x ∂volume, False := by
    filter_upwards [h'] with x hx
    linarith
  exact (ae_empty_iff.2 (by simp)) h''

/-- The hypothesis and conclusion of Erdős problem 908.  The source sentence
is read literally: every positive increment of `f` is measurable, and the
conclusion supplies a continuous function, an additive function, and a
residual function invariant under each positive translation almost
everywhere. -/
def DeBruijnErdos908 : Prop :=
  ∀ f : ℝ → ℝ,
    (∀ h : ℝ, 0 < h → Measurable (fun x : ℝ => f (x + h) - f x)) →
      ∃ g a r : ℝ → ℝ,
        Continuous g ∧
        AdditiveFunction a ∧
        TranslationInvariantAe r ∧
        ∀ x : ℝ, f x = g x + a x + r x

/-- A concrete proved control instance: the zero function satisfies the
increment-measurability hypothesis and has the evident decomposition into
three zero functions. -/
theorem zero_instance :
    (∀ h : ℝ, 0 < h →
      Measurable (fun x : ℝ => (0 : ℝ) + h - 0)) →
      ∃ g a r : ℝ → ℝ,
        Continuous g ∧
        AdditiveFunction a ∧
        TranslationInvariantAe r ∧
        ∀ x : ℝ, (0 : ℝ) = g x + a x + r x := by
  intro _
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, continuous_const, ?_, ?_, ?_⟩
  · intro x y
    simp
  · intro h hh
    filter_upwards [] with x
    rfl
  · intro x
    simp

/-- The affirmative resolution recorded by the source.  The formal
derivation of the full decomposition theorem is not reproduced here; this
declaration records the known result attributed in the source to Laczkovich. -/
theorem deBruijnErdos908_answer : DeBruijnErdos908 := by
  sorry

#print axioms additiveFunction_witness_pos
#print axioms additiveFunction_witness_neg
#print axioms additiveFunctionFinite_witness_pos
#print axioms additiveFunctionFinite_witness_neg
#print axioms translationInvariantAe_witness_pos
#print axioms translationInvariantAe_witness_neg
#print axioms zero_instance

end Erdos908
