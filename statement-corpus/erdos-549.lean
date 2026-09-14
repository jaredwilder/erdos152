/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
If $T$ is a tree which is a bipartite graph with $k$ vertices and $2k$ vertices in the other class then\[R(T)=4k-1.\]

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#549 : [EFRS82] graph theory | ramsey theory This is a special case of a conjecture of Burr [Bu74] (see [547] ). It follows from results in [EFRS82] that $R(T)\geq 4k-1$. This is false: Norin, Sun, and Zhao [NSZ16] have proved that if $T$ is the union of two stars on $k$ and $2k$ vertices, with an edge joining the centre of the two stars, then $R(T)\geq (4.2-o(1))k$, and conjectured that $R(T)=(4.2+o(1))k$. The best upper bound for the Ramsey number for this tree is $R(T)\leq (4.21526+o(1))k$, obtained using the flag algebra method by Norin, Sun, and Zhao [NSZ16] . Dubó and Stein [DuSt24] have given a short elementary proof of the weaker bound $R(T)\leq \lceil 4.27492k\rceil+1$ Montgomery, Pavez-Signé, and Yan [MPY25] have proved that $R(T)=4k-1$ if $T$ has maximum degree at most $ck$ for some constant $c>0$. Erdős, Faudree, Rousseau, and Schelp [EFRS82] proved that $R(T)=4k-1$ if $T$ is a 'broom', formed by identifying the centre of a star on $k+1$ vertices with an endpoint of a path on $2k$ vertices. Burr and Erdős [BuEr76] proved that $R(T)=4k-1$ if $T$ is formed by identifying one end of a path on $4$ vertices with the centre of a star on $k-1$ vertices, and the other endpoint with the centre of a star on $2k-1$ vertices. This problem is #15 in Ramsey Theory in the graphs problem collection. See also [547] . Additional thanks to : Louis DeBiasio and Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 28 December 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #549, https://www.erdosproblems.com/549, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos549

/-- A two-colouring of the ordered pairs of vertices of a complete graph.
The symmetry condition used below makes the colouring an undirected edge-colouring;
the diagonal values are irrelevant. -/
def EdgeColoring (n : ℕ) :=
  Fin n → Fin n → Bool

/-- The colour of every edge of a copy of `T` is required to be constant.
The map is injective, and graph edges of `T` map to edges of the prescribed colour.
This is the usual (not necessarily induced) monochromatic-copy condition. -/
def MonochromaticCopy {V : Type*} [Fintype V]
    (T : SimpleGraph V) (n : ℕ) (c : EdgeColoring n)
    (b : Bool) : Prop :=
  ∃ f : V → Fin n,
    Function.Injective f ∧
      ∀ ⦃u v : V⦄, T.Adj u v → c (f u) (f v) = b

/-- `RamseyGood T n` means that every symmetric red-blue colouring of the
edges of the complete graph on `n` vertices contains a monochromatic copy of
`T`. -/
def RamseyGood {V : Type*} [Fintype V]
    (T : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ c : EdgeColoring n,
    (∀ i j, c i j = c j i) →
      MonochromaticCopy T n c true ∨ MonochromaticCopy T n c false

/-- `IsRamseyNumber T n` says that `n` is the least positive-size threshold
with the Ramsey property.  This avoids using an unbounded `sInf`: the
definition is an explicit leastness statement and therefore has no default
value on an empty or unbounded set. -/
def IsRamseyNumber {V : Type*} [Fintype V]
    (T : SimpleGraph V) (n : ℕ) : Prop :=
  RamseyGood T n ∧ ∀ m < n, ¬ RamseyGood T m

/-- The source's assertion, formalized with a genuine finite simple graph,
its tree predicate, and an explicit bipartition.  `A` is one colour class,
and `Aᶜ` is the other class. -/
def OriginalClaim : Prop :=
  ∀ (V : Type) [Fintype V] (T : SimpleGraph V) (A : Finset V) (k : ℕ),
    T.IsTree →
      (∀ ⦃u v : V⦄, T.Adj u v →
        ((u ∈ A ∧ v ∉ A) ∨ (u ∉ A ∧ v ∈ A))) →
      A.card = k →
      (Finset.univ \ A).card = 2 * k →
      IsRamseyNumber T (4 * k - 1)

/-- A basic anti-vacuity control: a nonempty graph cannot have the Ramsey
property at `0`, because a monochromatic copy would require a function into
the empty type `Fin 0`. -/
theorem ramseyGood_zero_false
    {V : Type*} [Fintype V] (T : SimpleGraph V)
    (hV : Nonempty V) : ¬ RamseyGood T 0 := by
  classical
  intro h
  let c : EdgeColoring 0 := fun i j => Fin.elim0 i
  have hc : ∀ i j, c i j = c j i := by
    intro i
    exact Fin.elim0 i
  rcases h c hc with hred | hblue
  · rcases hred with ⟨f, hf, hcopy⟩
    rcases hV with ⟨v⟩
    exact Fin.elim0 (f v)
  · rcases hblue with ⟨f, hf, hcopy⟩
    rcases hV with ⟨v⟩
    exact Fin.elim0 (f v)

/-- The resolution records that the original universal equality is false.
The mathematical counterexample and its Ramsey-number estimate are supplied
by the cited external results; formalizing those estimates remains an
explicit gap here. -/
theorem originalClaim_false : ¬ OriginalClaim := by
  sorry Erdos549

#print axioms Erdos549.ramseyGood_zero_false
