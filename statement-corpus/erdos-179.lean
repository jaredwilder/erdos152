/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $1\leq k<\ell$ be integers and define $F_k(N,\ell)$ to be minimal such that every set $A\subset \mathbb{N}$ of size $N$ which contains at least $F_k(N,\ell)$ many $k$-term arithmetic progressions must contain an $\ell$-term arithmetic progression. Find good upper bounds for $F_k(N,\ell)$. Is it true that\[F_3(N,4)=o(N^2)?\]Is it true that for every $\ell>3$\[\lim_{N\to \infty}\frac{\log F_3(N,\ell)}{\log N}=2?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#179 : [Er73] [Er75b] [ErGr79] [Er80,p.93] [ErGr80] additive combinatorics | arithmetic progressions Erdős remarks the upper bound $o(N^2)$ is certainly false for $\ell >\epsilon \log N$. The answer is yes: Fox and Pohoata [FoPo20] have shown that, for all fixed $1\leq k<\ell$,\[F_k(N,\ell)=N^{2-o(1)}\]and in fact\[F_{k}(N,\ell) \leq \frac{N^2}{(\log\log N)^{C_\ell}}\]where $C_\ell>0$ is some constant. In fact, they show that, if $r_\ell(N)$ is the size of the largest subset of $\{1,\ldots,N\}$ without an $\ell$-term arithmetic progression then there exists some absolute constant $c>0$ such that\[\left(c \frac{r_\ell(N)}{N}\right)^{2(k-1)}N^2 < F_k(N,\ell) <\left(\frac{r_\ell(N)}{N}\right)^{O(1)}N^2.\]Any improved bounds for Szemerédi's theorem (see [139] ) therefore yield improved bounds for $F_k(N,\ell)$. In particular, the bounds of Leng, Sah, and Sawhney [LSS24] imply\[F_k(N,\ell) \leq \frac{N^2}{\exp((\log\log N)^{c_\ell})}\]for some constant $c_\ell>0\] 
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos179

/-- The finite-set model of a `k`-term arithmetic progression with initial term `a`
and positive common difference `d`. -/
def ArithmeticProgression (k a d : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => a + i * d)

/-- A finite set is a `k`-term arithmetic progression if it is represented by
some initial term and some positive common difference. -/
def IsArithmeticProgression (k : ℕ) (P : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ P = ArithmeticProgression k a d

/-- The number of distinct `k`-term arithmetic progressions contained in a finite
set `A`. The use of `A.powerset` makes the counted objects finite. -/
def progressionCount (A : Finset ℕ) (k : ℕ) : ℕ :=
  (A.powerset.filter (fun P => IsArithmeticProgression k P)).card

/-- The threshold property occurring in the definition of `F_k(N,ℓ)`: every
`N`-element finite set containing at least `t` counted `k`-term progressions
contains an `ℓ`-term progression. -/
def GoodThreshold (k ell N t : ℕ) : Prop :=
  ∀ A : Finset ℕ,
    A.card = N →
      t ≤ progressionCount A k →
        ∃ a d : ℕ, 0 < d ∧ ArithmeticProgression ell a d ⊆ A

/-- Existence of a threshold. This is the finite extremal assertion needed to
make the minimum in the source definition meaningful; its proof is left as an
explicit gap rather than hidden in a label. -/
theorem threshold_exists {k ell N : ℕ} (h : k < ell) :
    ∃ t : ℕ, GoodThreshold k ell N t := by
  sorry

/-- The source quantity `F_k(N,ℓ)`, modeled as the least natural threshold
satisfying `GoodThreshold`. Unlike an `sInf` definition, `Nat.find` has no
empty-set or unbounded-set default value; its existence is supplied explicitly
by `threshold_exists`. -/
noncomputable def F (k ell N : ℕ) (h : k < ell) : ℕ :=
  Nat.find (threshold_exists h)

/-- The value `F` satisfies the defining threshold property. -/
theorem F_spec {k ell N : ℕ} (h : k < ell) :
    GoodThreshold k ell N (F k ell N h) := by
  simpa [F] using Nat.find_spec (threshold_exists h)

/-- A basic control on the progression encoding: every one-term progression is
the singleton containing its initial term, independently of its positive
difference. -/
theorem arithmeticProgression_one (a d : ℕ) :
    ArithmeticProgression 1 a d = {a} := by
  ext x
  simp [ArithmeticProgression]

/-- The established asymptotic exponent statement recorded in the resolution:
for every fixed `ell > 3`, the logarithmic exponent of `F_3(N,ell)` tends to
`2`. The substantive additive-combinatorial input is retained as an explicit
sorry. -/
theorem logarithmic_exponent (ell : ℕ) (hell : 3 < ell) :
    Tendsto
      (fun N : ℕ =>
        Real.log (F 3 ell N (by omega) : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 (2 : ℝ)) := by
  sorry

/-- A formal upper-bound consequence stated in the natural-number scale of the
source: for fixed `k < ell`, some positive exponent of `log log N` gives an
eventual saving over `N²`. The existence of this saving is the recorded
Fox--Pohoata result; its proof is not reproduced here. -/
theorem eventual_loglog_upper_bound
    (k ell : ℕ) (h : k < ell) :
    ∃ C : ℕ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        F k ell N h ≤ N ^ 2 / (Nat.log (Nat.log N)) ^ C := by
  sorry Erdos179

#print axioms Erdos179.arithmeticProgression_one
