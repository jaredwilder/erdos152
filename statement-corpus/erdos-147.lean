import Mathlib

-- @category research solved

/-
Frozen source, verbatim:

NODE n000-question (question), VERBATIM:
If $H$ is bipartite with minimum degree $r$ then there exists $\epsilon=\epsilon(H)>0$ such that
\[\mathrm{ex}(n;H) \gg n^{2-\frac{1}{r-1}+\epsilon}.\]

NODE n001-resolution (resolution), VERBATIM:
#147 : [ErSi84] [Er93] [Er97c] graph theory | turan number Conjectured by Erdős and Simonovits [ErSi84] .
A probabilistic argument shows that there exists some $\epsilon=\epsilon(H)>0$ such that
\[\mathrm{ex}(n;H) \gg n^{2-\frac{2}{r}+\epsilon}.\]
This conjecture was disproved by Janzer [Ja23] for even $r\geq 4$.
The case $r=3$ was disproved by Janzer [Ja23b], who constructed, for any $\epsilon>0$,
a $3$-regular bipartite graph $H$ such that
\[\mathrm{ex}(n;H)\ll n^{\frac{4}{3}+\epsilon}.\]
In [Ja23] Janzer conjectures that the above lower bound is sharp, in that for any
$r\geq 3$ and $\epsilon>0$ there exists an $r$-regular graph $H$ such that
\[\mathrm{ex}(n;H) \ll n^{2-\frac{2}{r}+\epsilon}.\]
Janzer's result proves this for even $r\geq 4$.
-/

/-- A lower bound of the form `f(n) ≫ n^α`, expressed with explicit positive
constants and an eventual inequality. The use of `Real.rpow` formalizes real
exponents occurring in the source. -/
def ExtremalLowerBound (f : ℕ → ℝ) (α : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    c * Real.rpow (n : ℝ) α ≤ f n

/-- An upper bound of the form `f(n) ≪ n^α`, expressed with explicit positive
constants and an eventual inequality. -/
def ExtremalUpperBound (f : ℕ → ℝ) (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    f n ≤ C * Real.rpow (n : ℝ) α

/-- The original Erdős--Simonovits conjecture recorded in Problem 147.
The parameters `bipartite`, `minDegree`, and `ex` provide the graph-theoretic
interface absent from the basic Mathlib API. -/
def ErdősSimonovits147 {H : Type*}
    (bipartite : H → Prop)
    (minDegree : H → ℕ → Prop)
    (ex : H → ℕ → ℝ) : Prop :=
  ∀ h r, bipartite h → minDegree h r →
    ∃ ε : ℝ, 0 < ε ∧
      ExtremalLowerBound (fun n => ex h n)
        (2 - 1 / ((r : ℝ) - 1) + ε)

/-- The probabilistic lower-bound statement recorded in the resolution of
Problem 147. -/
def ProbabilisticBound147 {H : Type*}
    (bipartite : H → Prop)
    (minDegree : H → ℕ → Prop)
    (ex : H → ℕ → ℝ) : Prop :=
  ∀ h r, bipartite h → minDegree h r →
    ∃ ε : ℝ, 0 < ε ∧
      ExtremalLowerBound (fun n => ex h n)
        (2 - 2 / (r : ℝ) + ε)

/-- The source's statement that the original conjecture is disproved, represented
as the negation of its universal claim rather than asserted as a theorem. -/
def JanzerDisproof147 {H : Type*}
    (bipartite : H → Prop)
    (minDegree : H → ℕ → Prop)
    (ex : H → ℕ → ℝ) : Prop :=
  ¬ ErdősSimonovits147 bipartite minDegree ex

/-- Janzer's conjectured sharpness statement from the resolution, expressed
using an abstract predicate for regular graphs. -/
def JanzerSharpness147 {H : Type*}
    (regular : H → ℕ → Prop)
    (ex : H → ℕ → ℝ) : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ ε : ℝ, 0 < ε →
    ∃ h : H, regular h r ∧
      ExtremalUpperBound (fun n => ex h n)
        (2 - 2 / (r : ℝ) + ε)

/-- A basic proved control showing that the eventual lower-bound predicate is
inhabited in the degenerate constant case at exponent zero. -/
theorem extremalLowerBound_const_one :
    ExtremalLowerBound (fun _ : ℕ => (1 : ℝ)) 0 := by
  refine ⟨1, by norm_num, 0, ?_⟩
  intro n hn
  simp

/-- A basic proved control showing that the eventual upper-bound predicate is
also inhabited in the same constant case. -/
theorem extremalUpperBound_const_one :
    ExtremalUpperBound (fun _ : ℕ => (1 : ℝ)) 0 := by
  refine ⟨1, by norm_num, 0, ?_⟩
  intro n hn
  simp

#print axioms extremalLowerBound_const_one
#print axioms extremalUpperBound_const_one