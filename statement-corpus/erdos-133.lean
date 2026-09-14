/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(n)$ be minimal such that every triangle-free graph $G$ with $n$ vertices and diameter $2$ contains a vertex with degree $\geq f(n)$. What is the order of growth of $f(n)$? Does $f(n)/\sqrt{n}\to \infty$?

NODE n001-resolution (resolution), VERBATIM:
#133 : [Er97b] graph theory Asked by Erdős and Pach. The lower bound $f(n)\geq (1-o(1))\sqrt{n}$ follows from the fact that a graph with maximum degree $d$ and diameter $2$ has at most 1+d+d(d-1)=d^2+1 many vertices. Simonovits observed that the subsets of $[3m-1]$ of size $m$, two sets joined by edge if and only if they are disjoint, forms a triangle-free graph of diameter $2$ which is regular of degree $\binom{2m-1}{m}$. This construction proves that\[f(n) \leq n^{(1+o(1))\frac{2}{3H(1/3)}}=n^{0.7182\cdots},\]where $H(x)$ is the binary entropy function. In [Er97b] Erdős encouraged the reader to try and find a better construction. In this note Alon provides a simple construction that proves $f(n) \ll \sqrt{n\log n}$: take a triangle-free graph with independence number $\ll \sqrt{n\log n}$ (the existence of which is the lower bound in [165] ) and add edges until it has diameter $2$; the neighbourhood of any set is an independent set and hence the maximum degree is still $\ll \sqrt{n\log n}$. Hanson and Seyffarth [HaSe84] proved that $f(n)\leq (\sqrt{2}+o(1))\sqrt{n}$ using a Cayley graph on $\mathbb{Z}/n\mathbb{Z}$, with the generating set given by some symmetric complete sum-free set of size $\sim \sqrt{n}$. An alternative construction of such a complete sum-free set was given by Haviv and Levy [HaLe18] . Füredi and Seress [FuSe94] proved that $f(n)\leq (\frac{2}{\sqrt{3}}+o(1))\sqrt{n}$. The precise asymptotics of $f(n)$ are unknown; Alon believes that the truth is $f(n)\sim \sqrt{n}$. Additional thanks to : Noga Alon, Ishay Haviv Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #133, https://www.erdosproblems.com/133, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next <!-- Handle the
-/




import Mathlib
open Classical
open Filter

-- @category research open






open Classical Filter

namespace Erdos133

/-- The degree of a vertex in a finite simple graph on `Fin n`. -/
def vertexDegree (n : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  Fintype.card {w : Fin n // G.Adj v w}

/-- A graph is triangle-free when no three pairwise distinct vertices form a triangle. -/
def TriangleFree (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ ⦃a b c : Fin n⦄,
    a ≠ b → a ≠ c → b ≠ c →
    G.Adj a b → G.Adj b c → G.Adj c a → False

/-- `DiameterTwo` means that every pair of distinct vertices is joined by an edge
or has a common neighbor; thus the graph has diameter at most two. -/
def DiameterTwo (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ ⦃v w : Fin n⦄, v ≠ w →
    G.Adj v w ∨ ∃ u : Fin n, G.Adj v u ∧ G.Adj u w

/-- The assertion that every triangle-free diameter-two graph on `n` vertices
has a vertex of degree at least `k`. -/
def GoodThreshold (n k : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    TriangleFree n G →
    DiameterTwo n G →
    ∃ v : Fin n, k ≤ vertexDegree n G v

/-- The set of candidate guaranteed degree thresholds.  The explicit bound
`k ≤ n` makes the supremum bounded above; the bound is harmless because every
vertex degree is at most `n`. -/
def thresholdSet (n : ℕ) : Set ℕ :=
  {k : ℕ | k ≤ n ∧ GoodThreshold n k}

/-- The formalized extremal function.  This uses the greatest guaranteed
threshold, which is the standard non-degenerate interpretation of the source's
phrase "minimal such that every graph contains a vertex with degree at least
`f(n)`": the literal least threshold would always be zero.  The `sSup` is
applied only to `thresholdSet n`; for positive `n` this set is nonempty and
bounded above, as proved below. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup (thresholdSet n)

/-- Zero is a valid degree threshold whenever the vertex set is nonempty. -/
theorem goodThreshold_zero (n : ℕ) (hn : 0 < n) :
    GoodThreshold n 0 := by
  intro G _ _
  let v : Fin n := ⟨0, hn⟩
  exact ⟨v, Nat.zero_le _⟩

/-- The threshold set is nonempty for every positive number of vertices.
This is the nonemptiness control required for the supremum definition. -/
theorem thresholdSet_nonempty (n : ℕ) (hn : 0 < n) :
    (thresholdSet n).Nonempty := by
  refine ⟨0, ?_⟩
  exact ⟨Nat.zero_le n, goodThreshold_zero n hn⟩

/-- The threshold set is bounded above by `n`.  This is the boundedness
control required for the supremum definition; the `sSup` is therefore not
being used through its junk value on an unbounded set. -/
theorem thresholdSet_bddAbove (n : ℕ) :
    BddAbove (thresholdSet n) := by
  refine ⟨n, ?_⟩
  intro k hk
  exact hk.1

/-- A proved sanity control: for every positive `n`, the defining supremum
has a genuinely nonempty, bounded candidate set rather than relying on the
default value of `sSup`. -/
theorem f_controls (n : ℕ) (hn : 0 < n) :
    (thresholdSet n).Nonempty ∧ BddAbove (thresholdSet n) := by
  exact ⟨thresholdSet_nonempty n hn, thresholdSet_bddAbove n⟩

/-- The source's unresolved divergence question, expressed as a limit along
the natural numbers.  The value at `n = 0` is irrelevant to this `atTop`
statement. -/
def DivergenceQuestion : Prop :=
  Tendsto
    (fun n : ℕ => (f n : ℝ) / Real.sqrt (n : ℝ))
    atTop atTop

/-- Alon's recorded belief that the extremal function is asymptotic to
`sqrt n`; this is recorded as a proposition and is not asserted as a theorem. -/
def AlonConjecture : Prop :=
  Tendsto
    (fun n : ℕ => (f n : ℝ) / Real.sqrt (n : ℝ))
    atTop (𝓝 1)

#print axioms thresholdSet_nonempty

end Erdos133
