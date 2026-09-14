/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(m,n)$ be maximal such that any graph on $n$ vertices in which every induced subgraph on $m$ vertices has an independent set of size at least $\log n$ must contain an independent set of size at least $f(n)$. Estimate $f(n)$. In particular, is it true that $f((\log n)^2,n) \geq n^{1/2-o(1)}$? Is it true that $f((\log n)^3,n)\gg (\log n)^3$?

NODE n001-resolution (resolution), VERBATIM:
#804 : [Er91] graph theory A question of Erdős and Hajnal. Alon and Sudakov [AlSu07] proved that in fact\[\frac{(\log n)^2}{\log\log n}\ll f((\log n)^2,n) \ll (\log n)^2\]and\[f((\log n)^3,n)\asymp \frac{(\log n)^2}{\log\log n}.\]See also [805] . Additional thanks to : Noga Alon Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #804, https://www.erdosproblems.com/804, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





-- @category research solved






import Mathlib
open Classical Filter

namespace Erdos804

/-- An independent set in `G` is a finite set of vertices containing no adjacent
distinct vertices. -/
def IndependentSet {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) : Prop :=
  ∀ ⦃v w : Fin n⦄, v ∈ s → w ∈ s → v ≠ w → ¬G.Adj v w

/-- POSITIVE WITNESS: the two-element set is independent in the empty graph. -/
theorem independentSet_witness_pos :
    IndependentSet (⊥ : SimpleGraph (Fin 4)) ({0, 1} : Finset (Fin 4)) := by
  decide

/-- NEGATIVE WITNESS: the same two-element set is not independent after adding
exactly one edge, namely the edge between `0` and `1`. -/
def oneEdge : SimpleGraph (Fin 4) where
  Adj v w := (v = 0 ∧ w = 1) ∨ (v = 1 ∧ w = 0)
  symm := by
    intro v w h
    rcases h with ⟨hv, hw⟩ | ⟨hv, hw⟩
    · exact Or.inr ⟨hw, hv⟩
    · exact Or.inl ⟨hw, hv⟩
  loopless := by
    intro v h
    rcases h with ⟨hv, hw⟩ | ⟨hv, hw⟩
    · subst hv
      exact Fin.zero_ne_one hw
    · subst hv
      exact Fin.zero_ne_one hw.symm

/-- NEGATIVE WITNESS: this is a near miss for the positive witness, failing
only because the newly introduced edge joins its two vertices. -/
theorem independentSet_witness_neg :
    ¬IndependentSet oneEdge ({0, 1} : Finset (Fin 4)) := by
  intro h
  have hne : (0 : Fin 4) ≠ 1 := by decide
  exact h (by simp) (by simp) hne (by simp [oneEdge])

/-- Every `m`-vertex induced subgraph of `G` contains an independent set of
size at least the discrete logarithm of `n`. -/
def LocalCondition (m n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n), s.card = m →
    ∃ t : Finset (Fin n),
      t ⊆ s ∧ t.card ≥ Nat.log 2 n ∧ IndependentSet G t

/-- POSITIVE WITNESS: every two-vertex induced subgraph of the empty graph on
four vertices contains an independent set of size `log₂ 4 = 2`. -/
theorem localCondition_witness_pos :
    LocalCondition 2 4 (⊥ : SimpleGraph (Fin 4)) := by
  decide

/-- NEGATIVE WITNESS: adding one edge gives a near miss, since the induced
subgraph on its two endpoints has no independent set of size two. -/
theorem localCondition_witness_neg :
    ¬LocalCondition 2 4 oneEdge := by
  decide

/-- The finite extremal guarantee at parameters `m,n`: the largest `k ≤ n`
such that every graph satisfying `LocalCondition m n` has an independent set
of size at least `k`. This bounded maximum avoids any unbounded `sSup`
interpretation; its range is nonempty and finite by construction. -/
def extremalGuarantee (m n : ℕ) : ℕ :=
  (Finset.filter
      (fun k : ℕ =>
        ∀ G : SimpleGraph (Fin n),
          LocalCondition m n G →
            ∃ s : Finset (Fin n), s.card ≥ k ∧ IndependentSet G s)
      (Finset.range (n + 1))).sup id

/-- The finite definition agrees with the expected elementary control value:
for `m = 2` and `n = 4`, the local condition forces the empty graph, whose
largest independent set has size four. -/
theorem extremalGuarantee_control :
    extremalGuarantee 2 4 = 4 := by
  decide

/-- A discrete version of the source's function `f(m,n)`, using `Nat.log` and
the finite extremal guarantee above. -/
def f (m n : ℕ) : ℕ :=
  extremalGuarantee m n

/-- The source's recorded resolution, expressed with discrete logarithms:
up to multiplicative constants, the square-scale value is between
`(log n)^2 / (log log n + 1)` and `(log n)^2`, while the cube-scale value
has the same order as the former quantity. The analytic translation of the
source's asymptotic notation and the proof of these bounds remain to be
formalized. -/
theorem known_resolution :
    ∃ c : ℕ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      (Nat.log 2 n)^2 / (c * (Nat.log 2 (Nat.log 2 n) + 1))
          ≤ f ((Nat.log 2 n)^2) n ∧
      f ((Nat.log 2 n)^2) n ≤ c * (Nat.log 2 n)^2 ∧
      (Nat.log 2 n)^2 / (c * (Nat.log 2 (Nat.log 2 n) + 1))
          ≤ f ((Nat.log 2 n)^3) n ∧
      f ((Nat.log 2 n)^3) n
          ≤ c * (Nat.log 2 n)^2 / (Nat.log 2 (Nat.log 2 n) + 1) := by
  sorry Erdos804
