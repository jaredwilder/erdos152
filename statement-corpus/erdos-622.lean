/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $G$ be a regular graph with $2n$ vertices and degree $n+1$. Must $G$ have $\gg 2^{2n}$ subsets that are spanned by a cycle?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#622 : [Er99] graph theory A problem of Erdős and Faudree. Erdős writes 'it is easy to see' that there are at least $(\frac{1}{2}+o(1))2^{2n}$ sets that are not on a cycle. If the regularity condition is replaced by minimum degree $n+1$ then the answer is no (consider $K_{n,n}$ with a spanning star in each part). Similarly this is false with degree $n$, as $K_{n,n}$ shows. This has been resolved by Draganić, Keevash, and Müyesser [DKM25] , who prove the asymptotically tight result that there are at least\[(\tfrac{1}{2}+o(1))2^{2n}\]subsets which are spanned by a cycle. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #622, https://www.erdosproblems.com/622, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos622

/-- The successor of an index in a cyclically ordered finite set. -/
def nextFin (k : ℕ) (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩

/-- `CycleSpans G S` means that the vertex set `S` is exactly the set of vertices
appearing on an injectively parametrized cycle of length at least three in `G`. -/
def CycleSpans {V : Type} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∃ k : ℕ, 3 ≤ k ∧
    ∃ v : Fin k → V,
      Function.Injective v ∧
        (∀ i : Fin k,
          G.Adj (v i) (v (nextFin k (by omega) i))) ∧
          S = Set.range v

/-- The number of subsets of the finite vertex set that are spanned by a cycle. -/
noncomputable def cycleSubsetCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (Finset.univ.filter (fun S : Finset V => CycleSpans G (S : Set V))).card

/-- The literal asymptotic form of the question: one fixed positive proportion
of all subsets is spanned by a cycle, uniformly over regular graphs of the
specified order. -/
def Question622 : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
        Fintype.card V = 2 * n →
          (∀ v : V, G.degree v = n + 1) →
            (cycleSubsetCount G : ℝ) ≥ c * (2 : ℝ) ^ (2 * n)

/-- A proved control showing that `CycleSpans` is not an empty predicate:
the complete graph on three vertices spans its whole vertex set by a triangle. -/
theorem triangle_cycle_control :
    CycleSpans (⊤ : SimpleGraph (Fin 3)) (Set.univ : Set (Fin 3)) := by
  refine ⟨3, by norm_num, (fun i : Fin 3 => i), ?_, ?_, ?_⟩
  · exact Function.injective_id
  · intro i
    fin_cases i <;> decide
  · simp

#print axioms triangle_cycle_control

/-- The resolved asymptotic theorem recorded in the resolution node. The source
attributes this result to Draganić, Keevash, and Müyesser [DKM25]. The proof
of that literature theorem remains to be formalized here. The statement is a
lower bound, so default junk values of any supremum or infimum are irrelevant:
no `sSup` or `sInf` is used. -/
theorem resolved_cycle_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
          Fintype.card V = 2 * n →
            (∀ v : V, G.degree v = n + 1) →
              (cycleSubsetCount G : ℝ) ≥
                ((1 / 2 : ℝ) - ε) * (2 : ℝ) ^ (2 * n) := by
  sorry

/-- The original question follows from the recorded asymptotic theorem by
taking `ε = 1/4`, hence obtaining the positive constant `c = 1/4`. This
derivation is proved from the sorried literature input above; its remaining
axiom footprint therefore records that dependency. -/
theorem question622_answered : Question622 := by
  obtain ⟨N, hN⟩ := resolved_cycle_bound (1 / 4 : ℝ) (by norm_num)
  refine ⟨1 / 4, by norm_num, N, ?_⟩
  intro n hn V _ G hcard hregular
  have h := hN n hn V G hcard hregular
  norm_num at h ⊢
  exact h

#print axioms question622_answered

end Erdos622
