/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours needed to colour the vertices of $G$ such that each colour class induces either a complete graph or empty graph. Let $z(n)$ be the maximum value of $\zeta(G)$ over all graphs $G$ with $n$ vertices. Determine $z(n)$ for small values of $z(n)$. In particular is it true that $z(12)=4$?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#758 : [ErGi93] graph theory | chromatic number A question of Erdős and Gimbel, who knew that $4\leq z(12)\leq 5$ and $5\leq z(15)\leq 6$. The equality $z(12)=4$ would follow from proving that if $G$ is a graph on $12$ vertices such that both $G$ and its complement are $K_4$-free then either $\chi(G)\leq 4$ or $\chi(G^c)\leq 4$. In fact there do exist such graphs - Bhavik Mehta found computationally that there is exactly one (up to taking the complement) graph on $12$ vertices such that both $G$ and its complement are $K_4$-free with chromatic number $\geq 5$. This graph was explicitly checked to have cochromatic number $4$, and hence this proves that indeed $z(12)=4$. The values of $z(n)$ are now known for $1\leq n\leq 19$:\[1,1,2,2,3,3,3,3,4,4,4,4,5,5,5,6,6,6,6.\](The only significant difficulty here is proving $z(12)=4$ - the others follow from easy inductive arguments and the facts that $R(3)=6$ and $R(4)=18$.) It is unknown whether $z(20)=6$ or $7$. Gimbel [Gi86] has shown that $z(n) \asymp \frac{n}{\log n}$. Additional thanks to : Bhavik Mehta Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. Comments (0) Proof claims (0) More information and links ( View history ) OEIS Possible Reactions Likes ipitchford Open to collaboration None Currently working on ipitchford Looks difficult None Looks tractable ipitchford Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos758

/-- A colouring of a finite graph is cochromatic when every colour class
induces either a complete graph or an empty graph. -/
def IsCochromaticColouring {n k : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ c : Fin n → Fin k,
    ∀ i : Fin k,
      (∀ ⦃u v : Fin n⦄, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
      (∀ ⦃u v : Fin n⦄, c u = i → c v = i → u ≠ v → ¬ G.Adj u v)

/-- Every finite graph admits a cochromatic colouring, by assigning a
different colour to every vertex. -/
theorem exists_isCochromaticColouring {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ k : ℕ, IsCochromaticColouring G := by
  refine ⟨n, ?_⟩
  refine ⟨fun v => v, ?_⟩
  intro i
  right
  intro u v hu hv huv
  apply huv
  exact hu.trans hv.symm

/-- The cochromatic number of a graph, defined as the least number of colours
in a cochromatic colouring. -/
noncomputable def cochromaticNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Nat.find (exists_isCochromaticColouring G)

/-- The canonical colouring gives the elementary upper bound
$\zeta(G) \leq n$ for a graph on `n` vertices. -/
theorem cochromaticNumber_le {n : ℕ} (G : SimpleGraph (Fin n)) :
    cochromaticNumber G ≤ n := by
  unfold cochromaticNumber
  apply Nat.find_min'
  exact exists_isCochromaticColouring G
  exact exists_isCochromaticColouring G

/-- The extremal function `z(n)`, defined as the maximum cochromatic number
over all simple graphs with vertex set `Fin n`. -/
noncomputable def z (n : ℕ) : ℕ :=
  (Finset.univ : Finset (SimpleGraph (Fin n))).sup cochromaticNumber

/-- The settled value of the Erdős--Gimbel question at twelve vertices.
The resolution node reports that the unique relevant graph, together with
the accompanying computational check, proves this equality. The detailed
enumeration and verification of that graph remain an external computational
input to this formalization. -/
theorem z_twelve : z 12 = 4 := by
  sorry Erdos758
