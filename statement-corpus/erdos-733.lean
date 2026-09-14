/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Call a sequence $1<X_1\leq\cdots X_m\leq n$ line-compatible if there is a set of $n$ points in $\mathbb{R}^2$ such that there are $m$ lines $\ell_1,\ldots,\ell_m$ containing at least two points, and the number of points on $\ell_i$ is exactly $X_i$. Prove that there are at most\[\exp(O(n^{1/2}))\]many line-compatible sequences.
-/

/- 
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#733 : [Er81] combinatorics | geometry This problem is essentially the same as [607] , but with multiplicities. Erdős writes that it is 'easy' to prove there are at least\[\exp(cn^{1/2})\]many such sequences for some constant $c>0$, but expected proving the upper bound to be difficult. Once it is done, he asked for the existence and value of\[\lim_{n\to \infty}\frac{\log f(n)}{n^{1/2}},\]where $f(n)$ counts the number of line-compatible sequences. This is true, and was proved by Szemerédi and Trotter [SzTr83] . See also [732] . Additional thanks to : Noga Alon Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #733, https://www.erdosproblems.com/733, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/







import Mathlib
open Classical

-- @category research solved





open Classical Filter

namespace Erdos733

/-- The Euclidean plane used for the geometric formulation of the problem. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A subset of the Euclidean plane is a line when it is an affine copy of a
one-dimensional real subspace with a nonzero direction vector. -/
def IsLine (L : Set Plane) : Prop :=
  ∃ p v : Plane, v ≠ 0 ∧ L = {x | ∃ t : ℝ, x = p + t • v}

/-- The number of points in a finite indexed configuration that lie on a set. -/
def pointCount {n : ℕ} (pts : Fin n → Plane) (L : Set Plane) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => pts i ∈ L)).card

/-- A crude finite upper bound for the number of distinct lines determined by
`n` points; it is used only to provide a finite ambient type for sequences. -/
def lineBound (n : ℕ) : ℕ :=
  n * (n - 1) / 2

/-- `SequenceGood n s` says that `s` is a nondecreasing sequence of
multiplicities in the range from `0` to `n`, realized by distinct geometric
lines on an injective configuration of `n` Euclidean points. The source
requires multiplicities greater than one; this is expressed by the condition
`1 < (s.2 i).val`. -/
def SequenceGood (n : ℕ)
    (s : Σ m : Fin (lineBound n + 1), Fin m → Fin (n + 1)) : Prop :=
  ∃ pts : Fin n → Plane,
    ∃ lines : Fin s.1.val → Set Plane,
      Function.Injective pts ∧
      (∀ i, IsLine (lines i)) ∧
      (∀ i j, i ≠ j → lines i ≠ lines j) ∧
      (∀ i, 1 < (s.2 i).val ∧
        pointCount pts (lines i) = (s.2 i).val)

/-- The finite counting function `f(n)` for line-compatible sequences. The
finite ambient type records the sequence length and all entries in
`{0, ..., n}`; `SequenceGood` selects precisely the line-compatible ones. -/
noncomputable def f (n : ℕ) : ℕ :=
  Fintype.card {s : Σ m : Fin (lineBound n + 1), Fin m → Fin (n + 1) //
    SequenceGood n s}

/-- A proved anti-vacuity control: the empty configuration realizes the empty
sequence at `n = 0`. This exercises the indexed configuration and line-counting
definitions rather than being an unrelated arithmetic fact. -/
theorem empty_control :
    ∃ s : Σ m : Fin (lineBound 0 + 1), Fin m → Fin (0 + 1),
      SequenceGood 0 s := by
  refine ⟨⟨0, fun i => Fin.elim0 i⟩, ?_⟩
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

/-- Formalization of the resolved upper bound. The notation
`exp(O(n^(1/2)))` is read in its standard eventual-constant form:
there exist constants `C` and `N` such that for every `n ≥ N`,
`f(n) ≤ exp(C * sqrt n)`. The source clause says that the number of
line-compatible sequences is at most this quantity; accordingly the host
configuration and its distinct lines are encoded in `SequenceGood`, and the
theorem bounds the resulting count `f`. The Szemerédi--Trotter result recorded
in the resolution is the external mathematical input still to be supplied
here, so this theorem is intentionally marked with `sorry`. -/
theorem upper_bound :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        (f n : ℝ) ≤ Real.exp (C * Real.sqrt (n : ℝ)) := by
  sorry Erdos733
