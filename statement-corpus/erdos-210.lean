/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(n)$ be minimal such that the following holds. For any $n$ points in $\mathbb{R}^2$, not all on a line, there must be at least $f(n)$ many lines which contain exactly 2 points (called 'ordinary lines'). Does $f(n)\to \infty$? How fast?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#210 : [Er61,p.245] [Er75f,p.105] [Er81] [Er83c] [Er84] [Er85] geometry Conjectured by Erdős and de Bruijn. The Sylvester-Gallai theorem states that $f(n)\geq 1$. The fact that $f(n)\geq 1$ was conjectured by Sylvester in 1893. Erdős rediscovered this conjecture in 1933 and told it to Gallai who proved it. That $f(n)\to \infty$ was proved by Motzkin [Mo51] . Kelly and Moser [KeMo58] proved that $f(n)\geq\tfrac{3}{7}n$ for all $n$. This is best possible for $n=7$. Motzkin conjectured that for $n\geq 13$ there are at least $n/2$ such lines. Csima and Sawyer [CsSa93] proved a lower bound of $f(n)\geq \tfrac{6}{13}n$ when $n\geq 8$. Green and Tao [GrTa13] proved that $f(n)\geq n/2$ for sufficiently large $n$. (A proof that $f(n)\geq n/2$ for large $n$ was earlier claimed by Hansen but this proof was flawed.) The bound of $n/2$ is best possible for even $n$, since one could take $n/2$ points on a circle and $n/2$ points at infinity. Surprisingly, Green and Tao [GrTa13] show that if $n$ is odd (and sufficiently large) then $f(n)\geq 3\lfloor n/4\rfloor$. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 16 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #210, https://www.erdosproblems.com/210, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A003034 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/






import Mathlib
open Classical
open Filter

-- @category research solved






open Classical Filter

namespace Erdos210

/-- A point in the Euclidean plane, represented by its two Euclidean coordinates. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The determinant test for three points to be collinear. -/
def cross (a b c : Plane) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-- `onLine pts i j k` says that the point indexed by `k` lies on the line
through the points indexed by `i` and `j`. -/
def onLine {n : ℕ} (pts : Fin n → Plane) (i j k : Fin n) : Prop :=
  cross (pts i) (pts j) (pts k) = 0

/-- `ordinaryLine pts i j` says that the line through the distinct indexed
points `i` and `j` contains exactly two indexed points. -/
def ordinaryLine {n : ℕ} (pts : Fin n → Plane) (i j : Fin n) : Prop :=
  i ≠ j ∧ (Finset.univ.filter (fun k : Fin n => onLine pts i j k)).card = 2

/-- The number of ordinary lines, counted once by imposing `i < j` on their
two defining indices. -/
def ordinaryCount {n : ℕ} (pts : Fin n → Plane) : ℕ :=
  (Finset.univ.filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ ordinaryLine pts p.1 p.2)).card

/-- A configuration is admissible when its points are pairwise distinct and
some three of them are not collinear. -/
def Admissible {n : ℕ} (pts : Fin n → Plane) : Prop :=
  Function.Injective pts ∧
    ∃ i j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ¬ onLine pts i j k

/-- `Good n r` is the assertion that every admissible configuration of `n`
points has at least `r` ordinary lines. -/
def Good (n r : ℕ) : Prop :=
  ∀ pts : Fin n → Plane, Admissible pts → r ≤ ordinaryCount pts

/-- The bounded set whose infimum defines the literal extremal quantity.
The upper bound is included so that the `sInf` below is never relying on its
junk value for an unbounded set; nonemptiness is supplied by the trivial
lower bound `0`. -/
def goodSet (n : ℕ) : Set ℕ :=
  {r | Good n r ∧ r ≤ n.choose 2}

/-- The extremal number of ordinary lines in this formalization. -/
noncomputable def extremalCount (n : ℕ) : ℕ :=
  sInf (goodSet n)

/-- Zero is always a valid lower bound for the number of ordinary lines. -/
theorem good_zero (n : ℕ) : Good n 0 := by
  intro pts h
  exact Nat.zero_le _

/-- The defining set for `extremalCount n` is nonempty. -/
theorem goodSet_nonempty (n : ℕ) : (goodSet n).Nonempty := by
  refine ⟨0, ?_⟩
  exact ⟨good_zero n, Nat.zero_le _⟩

/-- The defining set for `extremalCount n` is bounded above by the imposed
finite pair-count bound. -/
theorem goodSet_bddAbove (n : ℕ) : BddAbove (goodSet n) := by
  refine ⟨n.choose 2, ?_⟩
  intro r hr
  exact hr.2

/-- A concrete non-collinear configuration exists: the three vertices
`(0,0)`, `(1,0)`, and `(0,1)` form a triangle. -/
theorem triangle_admissible :
    Admissible (fun i : Fin 3 =>
      match i.1 with
      | 0 => ![0, 0]
      | 1 => ![1, 0]
      | _ => ![0, 1]) := by
  let pts : Fin 3 → Plane := fun i =>
    match i.1 with
    | 0 => ![0, 0]
    | 1 => ![1, 0]
    | _ => ![0, 1]
  have hinj : Function.Injective pts := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pts]
  refine ⟨hinj, 0, 1, 2, by decide, by decide, by decide, ?_⟩
  simp [onLine, cross, pts]
  norm_num

/-- The source's asymptotic question, formalized as the assertion that the
extremal number tends to infinity. The literature resolution records this as
proved by Motzkin; the proof of that deep theorem remains to be supplied here. -/
theorem extremalCount_tendsto_atTop :
    Tendsto extremalCount atTop atTop := by
  sorry Erdos210

#print axioms Erdos210.good_zero
#print axioms Erdos210.goodSet_nonempty
#print axioms Erdos210.goodSet_bddAbove
#print axioms Erdos210.triangle_admissible
