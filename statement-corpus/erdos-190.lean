/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $H(k)$ be the smallest $N$ such that in any finite colouring of $\{1,\ldots,N\}$ (into any number of colours) there is always either a monochromatic $k$-term arithmetic progression or a rainbow arithmetic progression (i.e. all elements are different colours). Estimate $H(k)$. Is it true that\[H(k)^{1/k}/k \to \infty\]as $k\to\infty$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#190 : [ErGr79,p.333] [ErGr80,p.17] additive combinatorics | arithmetic progressions This type of problem belongs to 'canonical' Ramsey theory. The existence of $H(k)$ follows from Szemerédi's theorem, and it is easy to show that $H(k)^{1/k}\to\infty$. A recurrence of Hunter [Hu25b] implies $H(k)^{1/k} \to \infty$ (see Section 6 of [FoHu26] ). Bae [Ba26] proved more precisely that $H(k)\geq k^{(2-o(1))k}$. Fox and Hunter [FoHu26] independently obtained the stronger estimate\[H(k) \geq k^{(1-o(1))k\log k}.\] Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (5) Proof claims (0) More information and links This page was last edited 02 June 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #190, https://www.erdosproblems.com/190, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising harguiny Previous Next
-/



import Mathlib
open Classical
open Filter

-- @category research open







open Classical Filter

namespace Erdos190

/-- An arithmetic progression of length `k` in `{0, ..., N - 1}`, represented by
its starting point and common difference. -/
def IsArithmeticProgression (N k a d : ℕ) : Prop :=
  ∀ i : Fin k, a + d * i.1 < N

/-- A monochromatic `k`-term arithmetic progression for a colouring `col`. -/
def HasMonochromaticProgression (N k c : ℕ) (col : Fin N → Fin c) : Prop :=
  ∃ a d : ℕ,
    IsArithmeticProgression N k a d ∧
      ∀ i j : Fin k,
        col ⟨a + d * i.1, by
          exact IsArithmeticProgression N k a d i⟩ =
          col ⟨a + d * j.1, by
            exact IsArithmeticProgression N k a d j⟩

/-- A rainbow `k`-term arithmetic progression for a colouring `col`, meaning
that distinct terms receive distinct colours. -/
def HasRainbowProgression (N k c : ℕ) (col : Fin N → Fin c) : Prop :=
  ∃ a d : ℕ,
    IsArithmeticProgression N k a d ∧
      ∀ i j : Fin k, i ≠ j →
        col ⟨a + d * i.1, by
          exact IsArithmeticProgression N k a d i⟩ ≠
          col ⟨a + d * j.1, by
            exact IsArithmeticProgression N k a d j⟩

/-- `Good k N` says that every finite colouring of `{0, ..., N - 1}`,
with any finite number of colours, contains either a monochromatic or a
rainbow `k`-term arithmetic progression. -/
def Good (k N : ℕ) : Prop :=
  ∀ c : ℕ, ∀ col : Fin N → Fin c,
    HasMonochromaticProgression N k c col ∨
      HasRainbowProgression N k c col

/-- The set of thresholds defining `H(k)`. -/
def Thresholds (k : ℕ) : Set ℕ :=
  {N | Good k N}

/-- The Erdős canonical Ramsey threshold `H(k)`, defined as an infimum.
The definition uses `Nat.sInf`, so its intended mathematical use requires
that `Thresholds k` is nonempty; the latter is the content of the known
existence result coming from finite Ramsey theory and Szemerédi's theorem. -/
noncomputable def H (k : ℕ) : ℕ :=
  sInf (Thresholds k)

/-- The known existence assertion ensuring that the `sInf` defining `H(k)` is
not relying on the empty-set default value. -/
theorem thresholds_nonempty (k : ℕ) : (Thresholds k).Nonempty := by
  sorry

/-- A proved control exercising the definitions: for `k = 0` and `N = 0`,
the required alternative is vacuously satisfied. -/
theorem zero_mem_thresholds : Good 0 0 := by
  intro c col
  left
  refine ⟨0, 0, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i j
    exact Fin.elim0 i

/-- The question from the source, formalized as divergence to infinity of
`H(k)^(1/k) / k` along the natural numbers. -/
def Question : Prop :=
  Tendsto
    (fun k : ℕ =>
      Real.rpow (H k : ℝ) (1 / (k : ℝ)) / (k : ℝ))
    atTop atTop

/-- The recorded known result that `H(k)^(1/k)` tends to infinity. This is
separate from `Question`, which asks whether the stronger quotient by `k`
also tends to infinity. -/
def RecordedRootDivergence : Prop :=
  Tendsto
    (fun k : ℕ =>
      Real.rpow (H k : ℝ) (1 / (k : ℝ)))
    atTop atTop

/-- The source records `RecordedRootDivergence` as known, via Hunter's
recurrence and the cited work of Fox and Hunter; its proof is not reproduced
in this formalization. -/
theorem recorded_root_divergence : RecordedRootDivergence := by
  sorry Erdos190
