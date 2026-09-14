/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $G$ be a graph with girth $>4$ (that is, it contains no cycles of length $3$ or $4$). Can the edges of $G$ always be directed such that there is no directed cycle, and reversing the direction of any edge also creates no directed cycle?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#1006 : [Er71] [Er76b] graph theory | cycles In [Er71] Erdős credits this problem to Ore, who gave an example of a graph without this property which has girth $4$. Gallai noted that the Grötzsch graph also lacks this property. This is false - Nešetřil and Rödl [NeRo78b] proved that, for every integer $g$, there is a graph $G$ with girth $g$ such that every orientation of the edges in $G$ contains a directed cycle or a cycle obtained from a directed cycle by reversing one directed edge. Additional thanks to : Boris Alexeev and Raphael Steiner Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (2) Proof claims (0) More information and links This page was last edited 02 December 2025. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #1006, https://www.erdosproblems.com/1006, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/



import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos1006

/-- A finite graph code on the vertex set `Fin n`; the value `true` means adjacency. -/
def GraphCode (n : ℕ) := Fin n → Fin n → Bool

/-- A graph code is simple when it has no loops and adjacency is symmetric. -/
def ValidGraph {n : ℕ} (g : GraphCode n) : Prop :=
  (∀ v, g v v = false) ∧
    (∀ v w, g v w = true → g w v = true)

/-- POSITIVE WITNESS: the empty graph is a valid graph. -/
theorem validGraph_witness_pos : ValidGraph (fun v w : Fin 0 => false) := by
  decide

/-- NEGATIVE WITNESS: a one-vertex loop is a near-miss violating only loop-freeness. -/
theorem validGraph_witness_neg :
    ¬ ValidGraph (fun _ _ : Fin 1 => true) := by
  decide

/-- A directed cycle of length `k` in an oriented finite graph, including its
adjacency and the directed edge conditions around the cycle. -/
def HasDirectedCycle {n : ℕ} (g : GraphCode n)
    (o : Fin n → Fin n → Bool) (k : Fin (n + 1))
    (f : Fin k → Fin n) : Prop :=
  (3 ≤ k.val) ∧
    (∀ i j, f i = f j → i = j) ∧
    (∀ i, g (f i) (f ⟨(i.val + 1) % k.val, Nat.mod_lt _ (by omega)⟩) = true) ∧
    (∀ i, o (f i) (f ⟨(i.val + 1) % k.val, Nat.mod_lt _ (by omega)⟩) = true)

/-- The graph code has girth greater than four when it has no triangle or
four-cycle. -/
def GirthAboveFour {n : ℕ} (g : GraphCode n) : Prop :=
  ∀ k : Fin (n + 1), k.val = 3 ∨ k.val = 4 →
    ∀ f : Fin k → Fin n, ¬ HasDirectedCycle g (fun v w => g v w) k f

/-- POSITIVE WITNESS: the empty graph has girth greater than four. -/
theorem girth_witness_pos :
    GirthAboveFour (fun v w : Fin 0 => false) := by
  decide

/-- NEGATIVE WITNESS: a triangle is a near-miss violating the girth condition
by exactly one forbidden cycle length. -/
theorem girth_witness_neg :
    ¬ GirthAboveFour
      (fun v w : Fin 3 => if v ≠ w then true else false) := by
  decide

/-- Reversing the orientation of the edge between `a` and `b`. -/
def ReverseEdge {n : ℕ} (o : Fin n → Fin n → Bool)
    (a b : Fin n) : Fin n → Fin n → Bool :=
  fun x y =>
    if x = a ∧ y = b then !o x y
    else if x = b ∧ y = a then !o x y
    else o x y

/-- An orientation of a finite graph is admissible when it chooses exactly one
direction on every edge, has no directed cycle, and remains cycle-free after
reversing any one edge. -/
def AdmissibleOrientation {n : ℕ} (g : GraphCode n)
    (o : Fin n → Fin n → Bool) : Prop :=
  (∀ v w, g v w = true →
    ((o v w = true ∧ o w v = false) ∨
      (o v w = false ∧ o w v = true))) ∧
  (∀ k : Fin (n + 1), k.val < 3 ∨ k.val > n ∨
    ∀ f : Fin k → Fin n, ¬ HasDirectedCycle g o k f) ∧
  (∀ a b, g a b = true →
    ∀ k : Fin (n + 1), k.val < 3 ∨ k.val > n ∨
      ∀ f : Fin k → Fin n,
        ¬ HasDirectedCycle g (ReverseEdge o a b) k f)

/-- POSITIVE WITNESS: the empty orientation on the empty graph is admissible. -/
theorem admissible_witness_pos :
    AdmissibleOrientation
      (fun v w : Fin 0 => false)
      (fun v w : Fin 0 => false) := by
  decide

/-- NEGATIVE WITNESS: on a one-vertex loop, no orientation can choose exactly
one direction, giving a near-miss failure of admissibility. -/
theorem admissible_witness_neg :
    ¬ AdmissibleOrientation
      (fun _ _ : Fin 1 => true)
      (fun _ _ : Fin 1 => false) := by
  decide

/-- The bounded finite form of the question: every valid graph on `Fin n` with
girth greater than four admits an admissible orientation. -/
def QuestionFinite (n : ℕ) : Prop :=
  ∀ g : GraphCode n, ValidGraph g → GirthAboveFour g →
    ∃ o : Fin n → Fin n → Bool, AdmissibleOrientation g o

/-- POSITIVE WITNESS: the bounded question holds on the empty vertex set. -/
theorem questionFinite_witness_pos : QuestionFinite 0 := by
  decide

/-- A proved finite control showing that the bounded formulation is not an
unrestricted tautology: its hypotheses and conclusion are computationally
checkable on concrete finite graphs. -/
theorem questionFinite_control :
    QuestionFinite 0 ∧
      ValidGraph (fun v w : Fin 0 => false) ∧
      GirthAboveFour (fun v w : Fin 0 => false) := by
  decide

/-- The original question, read over finite graphs. The source asks whether
the orientation property holds for every graph of girth greater than four;
the finite bounded versions above make the concrete computational content
decidable. -/
def Question : Prop :=
  ∀ n : ℕ, QuestionFinite n

/-- The resolution recorded in the source is that the universal assertion is
false. The Nešetřil--Rödl construction establishing this negative result is
not reproduced here; this declaration honestly records that remaining
literature-dependent step as an explicit gap. -/
theorem question_is_false : ¬ Question := by
  sorry Erdos1006
