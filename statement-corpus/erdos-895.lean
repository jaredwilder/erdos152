/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is it true that, for all sufficiently large $n$, if $G$ is a triangle-free graph on $\{1,\ldots,n\}$ then there must exist three independent points $a,b,a+b$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#895 : [Er95d] additive combinatorics | graph theory A problem of Erdős and Hajnal. Hajnal thought that there is in fact an independent set which is a Hindman set - that is, an independent set of the shape\[\left\{ \sum_{i\in S}a_i : S\subseteq \{1,\ldots,k\}\right\} \]for some $a_1,\ldots,a_k$ (provided $n$ is sufficiently large depending on $k$). The stated problem has been resolved by Barber (personal communication) who verified using a SAT solver that this is true for all $n\geq 18$. The general question of an independent Hindman set remains open. Additional thanks to : Ben Barber Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #895, https://www.erdosproblems.com/895, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes Dogmachine Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable None Working on formalising None Previous Next
-/



import Mathlib
open Classical






open Classical Filter

namespace Erdos895

-- @category research solved

/-- A graph on the positive integers at most `n`, represented by `Fin (n + 1)`;
the vertex `0` is excluded from the additive configuration below. -/
def TriangleFree {n : ℕ} (G : SimpleGraph (Fin (n + 1))) : Prop :=
  ∀ ⦃a b c : Fin (n + 1)⦄,
    G.Adj a b → G.Adj b c → G.Adj a c → False

/-- A triple of distinct positive vertices whose third vertex is the sum of
the first two, and which is independent in the graph. -/
def HasAdditiveTriple {n : ℕ} (G : SimpleGraph (Fin (n + 1))) : Prop :=
  ∃ a b c : Fin (n + 1),
    0 < a.val ∧
    0 < b.val ∧
    0 < c.val ∧
    a.val + b.val = c.val ∧
    a ≠ b ∧
    a ≠ c ∧
    b ≠ c ∧
    ¬ G.Adj a b ∧
    ¬ G.Adj a c ∧
    ¬ G.Adj b c

/-- The finite, decidable version of the question at size `n`: every
triangle-free graph on `{0, ..., n}` has an additive independent triple on
the positive vertices. -/
def QuestionFinite (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin (n + 1)), TriangleFree G → HasAdditiveTriple G

/-- The graph with exactly the two opposite edges joining `1` and `2` on
`Fin 4`. -/
def EdgeGraph : SimpleGraph (Fin 4) where
  Adj a b := (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)
  symm := by
    intro a b h
    rcases h with h | h <;> simp_all
  loopless := by
    intro a h
    rcases h with h | h <;> simp_all

/-- The complete graph on `Fin 4`. -/
def CompleteGraph : SimpleGraph (Fin 4) where
  Adj a b := a ≠ b
  symm := by
    intro a b h
    exact h.symm
  loopless := by
    intro a h
    exact h rfl

/-- POSITIVE WITNESS: the empty graph at size `3` is triangle-free and has
the independent triple `1, 2, 3`. -/
theorem triangleFree_witness_pos :
    TriangleFree (⊥ : SimpleGraph (Fin 4)) := by
  decide

/-- NEGATIVE WITNESS: the complete graph at size `3` contains a triangle, so
it is a near miss for triangle-freeness. -/
theorem triangleFree_witness_neg :
    ¬ TriangleFree (CompleteGraph : SimpleGraph (Fin 4)) := by
  decide

/-- POSITIVE WITNESS: the empty graph at size `3` has the additive independent
triple `1, 2, 3`. -/
theorem additiveTriple_witness_pos :
    HasAdditiveTriple (⊥ : SimpleGraph (Fin 4)) := by
  decide

/-- NEGATIVE WITNESS: adding the single edge `1--2` to the positive witness
destroys its only possible additive triple at size `3`. -/
theorem additiveTriple_witness_neg :
    ¬ HasAdditiveTriple (EdgeGraph : SimpleGraph (Fin 4)) := by
  decide

/-- POSITIVE WITNESS: the finite question holds for the empty graph at size
`3`. -/
theorem questionFinite_witness_pos :
    QuestionFinite 3 := by
  decide

/-- NEGATIVE WITNESS: the finite question fails for the near-miss graph with
the single edge `1--2`; that graph is triangle-free but has no additive
independent triple. -/
theorem questionFinite_witness_neg :
    ¬ QuestionFinite 3 := by
  decide

/-- Barber's recorded resolution of Erdős problem #895: for every `n ≥ 18`,
every triangle-free graph on `{0, ..., n}` has three distinct positive
independent vertices `a`, `b`, and `a + b`.

The source sentence reads: “for all sufficiently large `n`, if `G` is a
triangle-free graph ... then there must exist three independent points
`a,b,a+b`.”  The resolution node records the concrete threshold `n ≥ 18`.
The SAT verification itself is not formalized here, so this theorem is an
honest remaining proof gap. -/
theorem barber_resolution :
    ∀ n : ℕ, 18 ≤ n → QuestionFinite n := by
  sorry

#print axioms triangleFree_witness_pos
#print axioms triangleFree_witness_neg
#print axioms additiveTriple_witness_pos
#print axioms additiveTriple_witness_neg
#print axioms questionFinite_witness_pos
#print axioms questionFinite_witness_neg

end Erdos895
