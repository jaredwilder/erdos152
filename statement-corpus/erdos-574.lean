/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Is it true that, for $k\geq 2$,\[\mathrm{ex}(n;\{C_{2k-1},C_{2k}\})=(1+o(1))(n/2)^{1+\frac{1}{k}}.\]

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#574 : [ErSi82] graph theory | turan number A problem of Erdős and Simonovits. This has been disproved a number of times. It appears to have been first disproved by Lazebnik, Ustimenko, and Woldar [LUW94b] for $k=3$ and $5$, since they construct bipartite graphs containing no $C_{2k}$ with\[\left(\frac{k-1}{k^{1+\frac{1}{k}}}+o(1)\right)n^{1+\frac{1}{k}}\]edges. (Note that the constant here for $k=3$ and $5$ is $\approx 0.462$ and $\approx 0.579$ respectively, while this problem predicts $\approx 0.396$ and $\approx 0.435$.) An alternative disproof for $k=3$ is given by Füredi, Naor, and Verstraëte [FNV06] , who prove that the extremal number for an $m\times 2m$ bipartite graph containing $C_6$ is (with $n=3m$)\[(2/3^{4/3}+o(1))n^{4/3}.\]See also [572] , [573] for the specific case of $k=2$, and [1080] . This problem is #49 in Extremal Graph Theory in the graphs problem collection. Additional thanks to : Boris Alexeev Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. Comments (1) Proof claims (0) More information and links This page was last edited 01 April 2026. ( View history ) View the LaTeX source When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #574, https://www.erdosproblems.com/574, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/






import Mathlib
open Classical
open Filter

-- @category research solved





open Classical Filter

namespace Erdos574

/-- The number of ordered adjacent pairs in a finite simple graph, divided by two.
This is the ordinary number of edges, represented using the real graph object
`SimpleGraph (Fin n)`. -/
def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  ((Finset.univ.filter
    (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ G.Adj p.1 p.2)).card) / 2

/-- A cyclic embedding of a cycle of length `l` into `G`: the vertices are
distinct and consecutive cyclic vertices are adjacent. The parameter `hl`
explicitly records that the cycle length is positive. -/
def CycleEmbedding {n l : ℕ} (G : SimpleGraph (Fin n)) (hl : 0 < l) : Prop :=
  ∃ f : Fin l → Fin n,
    Function.Injective f ∧
      ∀ i : Fin l,
        G.Adj (f i)
          (f ⟨(i.val + 1) % l, Nat.mod_lt _ hl⟩)

/-- `Avoids G k` means that the graph `G` contains neither a cycle of length
`2k - 1` nor a cycle of length `2k`. -/
def Avoids {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ¬ CycleEmbedding G (by omega : 0 < 2 * k - 1) ∧
  ¬ CycleEmbedding G (by omega : 0 < 2 * k)

/-- The Turán number for the two forbidden cycle lengths in the source.
The supremum is taken over the edge counts of genuine finite simple graphs on
`Fin n`, not over a tag or auxiliary classification. -/
noncomputable def extremalNumber (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), Avoids G k ∧ edgeCount G = m}

/-- The scale appearing in the source's asymptotic formula. -/
def asymptoticScale (k n : ℕ) : ℝ :=
  Real.rpow ((n : ℝ) / 2) (1 + (1 : ℝ) / k)

/-- The literal formal reading of `(1 + o(1))(n/2)^(1+1/k)`: the quotient of
the extremal number by the displayed scale tends to one along the natural
numbers. -/
def AsymptoticFormula (k : ℕ) : Prop :=
  Tendsto
    (fun n : ℕ => (extremalNumber k n : ℝ) / asymptoticScale k n)
    atTop (𝓝 1)

/-- The question from the source, restricted exactly to `k ≥ 2`. -/
def ErdosQuestion : Prop :=
  ∀ k : ℕ, 2 ≤ k → AsymptoticFormula k

/-- The empty graph has zero edges. This is a proved sanity check on the
file's graph and edge-count definitions. -/
theorem edgeCount_bot (n : ℕ) : edgeCount (⊥ : SimpleGraph (Fin n)) = 0 := by
  simp [edgeCount]

/-- Every graph has at most `n²` edges under the ordered-pair definition used
here. In particular, the set entering `sSup` is bounded above. -/
theorem edgeCount_le {n : ℕ} (G : SimpleGraph (Fin n)) :
    edgeCount G ≤ n * n := by
  unfold edgeCount
  calc
    ((Finset.univ.filter
        (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ G.Adj p.1 p.2)).card) / 2
        ≤ (Finset.univ.filter
          (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ G.Adj p.1 p.2)).card :=
      Nat.div_le_self _ _
    _ ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
      Finset.card_filter_le
    _ = n * n := by simp

/-- The defining set for `extremalNumber k n` is nonempty and bounded above.
Thus the `sSup` used in the definition is not relying on its empty-set or
unbounded-set junk value. -/
theorem extremalNumber_spec_control (k n : ℕ) :
    (Set.Nonempty
      {m : ℕ | ∃ G : SimpleGraph (Fin n), Avoids G k ∧ edgeCount G = m}) ∧
      BddAbove
        {m : ℕ | ∃ G : SimpleGraph (Fin n), Avoids G k ∧ edgeCount G = m} := by
  constructor
  · refine ⟨0, ?_⟩
    refine ⟨⊥, ?_, edgeCount_bot n⟩
    simp [Avoids, CycleEmbedding]
  · refine ⟨n * n, ?_⟩
    rintro m ⟨G, hG, rfl⟩
    exact edgeCount_le G

/-- The source records the asymptotic assertion as disproved. A complete
formal proof of the literature counterexample is not reproduced here; the
remaining gap is precisely the theorem that the displayed asymptotic
assertion fails, rather than a hidden axiom or a tagged substitute. -/
theorem source_resolution : ¬ ErdosQuestion := by
  sorry Erdos574
