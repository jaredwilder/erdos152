/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $\alpha$ be a cardinal or ordinal number or an order type such that every two-colouring of $K_\alpha$ contains either a red $K_\alpha$ or a blue $K_3$. For every $n\geq 3$ must every two-colouring of $K_\alpha$ contain either a red $K_\alpha$ or a blue $K_n$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#118 : [Er87] [Er90] [Er95d] [Er97f] set theory | ramsey theory Such $\alpha$ are called partition ordinals. Conjectured by Erdős and Hajnal. In arrow notation, this is asking where $\alpha \to (\alpha,3)^2$ implies $\alpha \to (\alpha, n)^2$ for every finite $n$. The answer is no, as independently shown by Schipperus [Sc99] (published in [Sc10] ) and Darby [Da99] . For example, Larson [La00] has shown that this is false when $\alpha=\omega^{\omega^2}$ and $n=5$. There is more background and proof sketches in Chapter 2.9 of [HST10] , by Hajnal and Larson. See also [590] , [591] , and [592] for more on partition ordinals. Additional thanks to : Zachary Chase, Andr\'{e}s Caicedo Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 17 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #118, https://www.erdosproblems.com/118, accessed 2026-08-30 From the external database . You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/



import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos118

/-- A two-colouring of the complete graph on `V`, represented by Boolean edge
colours together with symmetry. The diagonal colour is irrelevant. -/
structure TwoColoring (V : Type*) where
  color : V → V → Bool
  symmetric : ∀ x y, color x y = color y x

/-- Every edge between distinct vertices is red. -/
def RedClique {V : Type*} (c : TwoColoring V) : Prop :=
  ∀ x y, x ≠ y → c.color x y = true

/-- The colouring contains a blue complete graph on `n` vertices. -/
def BlueClique {V : Type*} (c : TwoColoring V) (n : Nat) : Prop :=
  ∃ f : Fin n → V,
    Function.Injective f ∧
      ∀ ⦃i j : Fin n⦄, i ≠ j → c.color (f i) (f j) = false

/-- The finite arrow relation used here: `Arrow c n` means that the colouring
has either a red clique on all vertices or a blue `K_n`. -/
def Arrow {V : Type*} (c : TwoColoring V) (n : Nat) : Prop :=
  RedClique c ∨ BlueClique c n

/-- The source question, expressed using the complete-graph colouring relation:
does the `K_3` conclusion imply every finite `K_n` conclusion for `n ≥ 3`? -/
def Question : Prop :=
  ∀ (V : Type*), (∀ c : TwoColoring V, Arrow c 3) →
    ∀ n : Nat, 3 ≤ n → ∀ c : TwoColoring V, Arrow c n

/-- A blue clique can be restricted along `m ≤ n`; this is a basic
monotonicity control for the finite clique predicate. -/
theorem blueClique_mono {V : Type*} {c : TwoColoring V} {m n : Nat}
    (h : m ≤ n) (hc : BlueClique c n) : BlueClique c m := by
  rcases hc with ⟨f, hf, hblue⟩
  let e : Fin m → Fin n := fun i => Fin.castLE h i
  refine ⟨fun i => f (e i), ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact congrArg Fin.val (hf (by
      intro heq
      apply hij
      apply Fin.ext
      exact congrArg Fin.val heq))
  · intro i j hij
    apply hblue
    intro heq
    apply hij
    apply Fin.ext
    exact congrArg Fin.val heq

/-- A proved sanity control: the constant-red colouring on `Fin 4` satisfies
the arrow conclusion for every requested clique size, because its red clique
is the whole vertex set. -/
def redColoring (V : Type*) : TwoColoring V where
  color := fun _ _ => true
  symmetric := by
    intro x y
    rfl

/-- The constant-red control exercises the red-clique branch of `Arrow`. -/
theorem red_control : Arrow (redColoring (Fin 4)) 5 := by
  left
  intro x y hxy
  rfl

/-- The resolution recorded in the source is negative: there are partition
ordinals for which the `K_3` arrow property does not imply the `K_n` arrow
property for every finite `n ≥ 3`. The source gives
`α = ω^(ω^2)` and `n = 5` as an example. A full formalization of cardinal and
ordinal partition relations remains to be supplied here. -/
theorem resolution : ¬ Question := by
  sorry Erdos118
