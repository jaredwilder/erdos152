/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
How large should $\ell(n)$ be such that, almost surely, a random $3$-uniform hypergraph on $3n$ vertices with $\ell(n)$ edges must contain $n$ vertex-disjoint edges?

NODE n001-resolution (resolution), VERBATIM:
#747 : [Er81] combinatorics | hypergraphs Asked to Erdős by Shamir in 1979. This is often known as Shamir's problem. Erdős writes: 'Many of the problems on random hypergraphs can be settled by the same methods as used for ordinary graphs and usually one can guess the answer almost immediately. Here we have no idea of the answer.' This is now essentially completely understood: Johansson, Kahn, and Vu [JKV08] proved that the threshold is $\ell(n)\asymp n\log n$. The precise asymptotic was given by Kahn [Ka23] , proving that the threshold is $\sim n\log n$ (also for the general problem over $r$-uniform hypergraphs). Additional thanks to : Mehtaab Sawhney Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #747, https://www.erdosproblems.com/747, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos747

/-- A vertex of a 3-uniform hypergraph on `3 * n` vertices. -/
abbrev Vertex (n : ℕ) := Fin (3 * n)

/-- A 3-element subset of the vertex set of a 3-uniform hypergraph. -/
def Edge (n : ℕ) := {e : Finset (Vertex n) // e.card = 3}

/-- A 3-uniform hypergraph on `3 * n` vertices, represented by its finite edge set. -/
def Hypergraph (n : ℕ) := Finset (Edge n)

/-- `HasPerfectMatching n H` means that `H` contains `n` pairwise vertex-disjoint edges. -/
def HasPerfectMatching (n : ℕ) (H : Hypergraph n) : Prop :=
  ∃ M : Finset (Edge n),
    M.card = n ∧
      (∀ e ∈ M, e ∈ H) ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e.1 f.1)

/-- The finite sample space of hypergraphs having exactly `k` edges. -/
noncomputable def HypergraphsOfSize (n k : ℕ) : Finset (Hypergraph n) := by
  classical
  exact (Finset.univ : Finset (Hypergraph n)).filter (fun H => H.card = k)

/-- The uniform probability that a hypergraph with `k` edges contains `n` disjoint edges.

The quotient is interpreted as `0` when the finite sample space is empty; this does not
affect the asymptotic statement below, whose source meaning concerns the large-`n` regime. -/
noncomputable def matchingProbability (n k : ℕ) : ℝ := by
  classical
  let S := HypergraphsOfSize n k
  exact
    ((S.filter (fun H => HasPerfectMatching n H)).card : ℝ) / (S.card : ℝ)

/-- The precise threshold assertion encoded by the resolution: below every fixed constant
multiple of `n * log n` the matching probability tends to zero, while above every fixed
constant multiple it tends to one. This is the formal reading of the source's statement
that the threshold is `∼ n log n`; the source sentence says a random hypergraph has
`ell(n)` edges and contains `n` vertex-disjoint edges, so the host is the random hypergraph
and the matching is the contained family of edges. -/
def ThresholdAsymptotic : Prop :=
  (∀ c : ℝ, 0 < c → c < 1 →
    Tendsto
      (fun n : ℕ => matchingProbability n ⌊c * (n : ℝ) * Real.log (n : ℝ)⌋₊)
      atTop (𝓝 0)) ∧
  (∀ c : ℝ, 1 < c →
    Tendsto
      (fun n : ℕ => matchingProbability n ⌊c * (n : ℝ) * Real.log (n : ℝ)⌋₊)
      atTop (𝓝 1))

/-- A proved anti-vacuity control: a nonempty matching cannot occur in the empty
hypergraph when `n > 0`. -/
theorem no_matching_empty {n : ℕ} (hn : 0 < n) :
    ¬ HasPerfectMatching n (∅ : Hypergraph n) := by
  rintro ⟨M, hcard, hsub, hdisj⟩
  have hM : M = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro e he
    have he' : e ∈ (∅ : Hypergraph n) := hsub e he
    simpa using he'
  rw [hM] at hcard
  simp at hcard
  omega

/-- Resolution of Erdős problem #747. The source records this as settled by
Johansson--Kahn--Vu and Kahn. The remaining formal gap is the probabilistic
threshold theorem itself, represented here by `ThresholdAsymptotic`. -/
theorem kahn_threshold : ThresholdAsymptotic := by
  sorry Erdos747
