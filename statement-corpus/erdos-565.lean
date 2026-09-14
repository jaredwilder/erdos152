/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $R^*(G)$ be the induced Ramsey number: the minimal $m$ such that there is a graph $H$ on $m$ vertices such that any $2$-colouring of the edges of $H$ contains an induced monochromatic copy of $G$. Is it true that\[R^*(G) \leq 2^{O(n)}\]for any graph $G$ on $n$ vertices?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#565 : [Er75d] graph theory | ramsey theory A problem of Erdős and Rödl. Even the existence of $R^*(G)$ is not obvious, but was proved independently by Deuber [De75] , Erdős, Hajnal, and Pósa [EHP75] , and Rödl [Ro73] . Rödl [Ro73] proved this when $G$ is bipartite. Kohayakawa, Prömel, and Rödl [KPR98] have proved that\[R^*(G) < 2^{O(n(\log n)^2)}.\]An alternative (and more explicit) proof was given by Fox and Sudakov [FoSu08] . Conlon, Fox, and Sudakov [CFS12] have improved this to\[R^*(G) < 2^{O(n\log n)}.\]This is true, and an upper bound of\[R^*(G) < 2^{O(n)}\]was proved by Aragão, Campos, Dahia, Filipe, and Marciano [ACDFM25] . This problem is #36 in Ramsey Theory in the graphs problem collection. Additional thanks to : Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 18 January 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #565, https://www.erdosproblems.com/565, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/



import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos565

/-- A symmetric assignment of one of two colours to every ordered pair of vertices.
The values on non-edges are irrelevant, so this is an extension of an edge-colouring. -/
def SymmetricTwoColoring {m : ℕ} (H : SimpleGraph (Fin m)) :=
  {χ : Fin m → Fin m → Bool // ∀ u v, χ u v = χ v u}

/-- The graph `G` occurs as an induced monochromatic copy in colour `c` inside `H`
through the injective vertex map `f`. -/
def IsInducedMonochromaticCopy {n m : ℕ}
    (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (χ : Fin m → Fin m → Bool) (f : Fin n → Fin m) (c : Bool) : Prop :=
  Function.Injective f ∧
    ∀ u v, G.Adj u v ↔ H.Adj (f u) (f v) ∧ χ (f u) (f v) = c

/-- `RamseyWitness H G` means that every symmetric two-colouring of the edges of
the host graph `H` contains an induced monochromatic copy of `G`. -/
def RamseyWitness {n m : ℕ} (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ χ : SymmetricTwoColoring H,
    ∃ f : Fin n → Fin m, ∃ c : Bool,
      IsInducedMonochromaticCopy G H χ.1 f c

/-- The existence predicate for an induced Ramsey host on exactly `m` vertices. -/
def HasInducedRamsey {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : Prop :=
  ∃ H : SimpleGraph (Fin m), RamseyWitness H G

/-- The induced Ramsey number, with the fallback value `0` only if existence
fails. The resolution node records that existence is known, and the separate
theorem `exists_induced_ramsey` supplies that mathematical input. -/
noncomputable def inducedRamseyNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  if h : ∃ m, HasInducedRamsey G m then Nat.find h else 0

/-- A proved sanity control: the empty graph on zero vertices has an induced
Ramsey host on zero vertices. This exercises the definitions without asserting
the substantive Ramsey theorem. -/
theorem empty_has_induced_ramsey :
    HasInducedRamsey (⊥ : SimpleGraph (Fin 0)) 0 := by
  refine ⟨⊥, ?_⟩
  intro χ
  refine ⟨(fun u : Fin 0 => Fin.elim0 u), ?_, false, ?_⟩
  · intro u v
    exact Fin.elim0 u
  · intro u v
    exact Fin.elim0 u

/-- The existence of the induced Ramsey number for every finite graph, as
proved independently in the references recorded by the resolution node.
The formal proof of this literature theorem remains to be supplied. -/
theorem exists_induced_ramsey {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ m, HasInducedRamsey G m := by
  sorry

/-- The source asks whether the induced Ramsey number is at most exponential in
the number of vertices. Here `2 ^ (C * n)` is the explicit formal reading of
`2^{O(n)}`: the constants `C` and `n₀` are uniform over all graphs, and the
bound is required for every `n ≥ n₀`.

Source-to-formal mapping: the source says “for any graph `G` on `n` vertices”;
this is represented by every `SimpleGraph (Fin n)`. The resolution records that
the answer is true and that an exponential upper bound was proved by
Aragão, Campos, Dahia, Filipe, and Marciano. The proof of that result is not
reconstructed here. -/
theorem exponential_upper_bound :
    ∃ C n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n),
      inducedRamseyNumber G ≤ 2 ^ (C * n) := by
  sorry

#print axioms empty_has_induced_ramsey

end Erdos565
