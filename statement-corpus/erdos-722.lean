/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k>r$ and $n$ be sufficiently large in terms of $k$ and $r$. Does there always exist a block $r-(n,k,1)$ design (or Steiner system with parameters $(n,k,r)$), provided the trivial necessary divisibility conditions $\binom{k-i}{r-i}\mid \binom{n-i}{r-i}$ are satisfied for every $0\leq i<r$? That is, can one find a family of $\binom{n}{k}\binom{k}{r}^{-1}$ many subsets of $\{1,\ldots,n\}$, all of size $k$, such that any $A\subseteq \{1,\ldots,n\}$ of size $r$ is contained in exactly one set in the family?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#722 : [Er81] combinatorics This was proved for $(r,k)$ by: Kirkman for $(2,3)$; Hanani [Ha61] for $(3,4)$, $(2,4)$, and $(2,5)$; Wilson [Wi72] for $(2,k)$ for any $k$; Keevash [Ke14] for all $(r,k)$. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #722, https://www.erdosproblems.com/722, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos722

/-- The divisibility conditions appearing in the source: every lower-dimensional
necessary divisibility condition is required. -/
def NecessaryDivisibility (n k r : ℕ) : Prop :=
  ∀ i, i < r →
    Nat.choose (k - i) (r - i) ∣ Nat.choose (n - i) (r - i)

/-- A block design on the finite point set `Fin n`.  The blocks are represented
by a finite family of finite subsets, every block has size `k`, and every
`r`-subset is contained in exactly one block. -/
def IsBlockDesign (n k r : ℕ) (blocks : Finset (Finset (Fin n))) : Prop :=
  (∀ b ∈ blocks, b.card = k) ∧
    (∀ A : Finset (Fin n), A.card = r →
      (blocks.filter (fun b => A ⊆ b)).card = 1)

/-- The intended mathematical question, with the number of blocks omitted
because it follows from the exact coverage condition and is more naturally
expressed as `choose n r / choose k r`.  The source's displayed count is
recorded separately as `LiteralBlockDesign`. -/
def Question : Prop :=
  ∀ k r, r < k →
    ∃ N, ∀ n, N ≤ n →
      NecessaryDivisibility n k r →
        ∃ blocks : Finset (Finset (Fin n)), IsBlockDesign n k r blocks

/-- The source's displayed block count, read literally as
`choose n k / choose k r`.  This is kept separate because the standard
Steiner-system count is instead `choose n r / choose k r`. -/
def LiteralBlockDesign (n k r : ℕ)
    (blocks : Finset (Finset (Fin n))) : Prop :=
  IsBlockDesign n k r blocks ∧
    blocks.card = Nat.choose n k / Nat.choose k r

/-- A sanity-check design: the unique 2-subset of `Fin 2` is a
`1-(2,2,1)` design. -/
theorem control_design_2 :
    ∃ blocks : Finset (Finset (Fin 2)), IsBlockDesign 2 2 1 blocks := by
  refine ⟨{Finset.univ}, ?_⟩
  decide

/-- The literal block count in the frozen source is not the standard count:
at `(n,k,r) = (2,2,1)`, the genuine design exists but no design can also
have the displayed literal cardinality `choose 2 2 / choose 2 1 = 0`. -/
theorem control_literal_count :
    ¬ ∃ blocks : Finset (Finset (Fin 2)), LiteralBlockDesign 2 2 1 blocks := by
  decide

/-- The corrected formalization of the result recorded in the resolution node.
The proof of the general existence theorem of Kirkman--Hanani--Wilson--Keevash
is not reproduced here; this declaration records that external mathematical
input honestly as an explicit proof gap. -/
theorem keevash_existence : Question := by
  sorry Erdos722

#print axioms Erdos722.control_design_2
#print axioms Erdos722.control_literal_count
