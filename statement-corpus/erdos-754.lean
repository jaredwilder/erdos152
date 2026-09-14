/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(n)$ be maximal such that there exists a set $A$ of $n$ points in $\mathbb{R}^4$ in which every $x\in A$ has at least $f(n)$ points in $A$ equidistant from $x$. Is it true that $f(n)\leq \frac{n}{2}+O(1)$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#754 : [Er94b] geometry | distances Avis, Erdős, and Pach [AEP88] proved that\[\frac{n}{2}+2 \leq f(n) \leq (1+o(1))\frac{n}{2}.\]This was proved by Swanepoel [Sw13] , who in fact proved more generally that, in any finite set $A\subset \mathbb{R}^4$ of size $n$ and any choice of distance $d(x)$ for each $x\in A$,\[\sum_{x\in A}\sum_{y\in A}1_{\lvert x-y\rvert =d(x)}\leq \tfrac{1}{2}n^2+O(n),\]and proved similar results for finite point sets in higher dimensional space. Additional thanks to : Liu Dingyuan Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #754, https://www.erdosproblems.com/754, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos754

abbrev Plane : Type := EuclideanSpace ℝ (Fin 4)

/-- The number of points of `A` distinct from `x` and at distance `d` from `x`. -/
def equidistantCount (A : Finset Plane) (x : Plane) (d : ℝ) : ℕ :=
  (A.filter (fun y => y ≠ x ∧ dist x y = d)).card

/-- `Admissible n k` says that a finite set of exactly `n` points in Euclidean
four-space gives every one of its points at least `k` other equidistant points. -/
def Admissible (n k : ℕ) : Prop :=
  ∃ A : Finset Plane,
    A.card = n ∧
      ∀ x ∈ A, ∃ d : ℝ, k ≤ equidistantCount A x d

/-- The literal extremal quantity from the source, with the harmless convention
`f 0 = 0`.  For positive `n` this is an `sSup`; the relevant set is bounded above
by `n` and is nonempty because `0` is admissible.  The `sSup` convention is
therefore not being used to extract mathematics from an empty or unbounded set. -/
noncomputable def f (n : ℕ) : ℕ :=
  if h : 0 < n then sSup {k : ℕ | Admissible n k} else 0

/-- Every admissible positive-size configuration has at most `n` equidistant
points at any chosen distance. -/
theorem admissible_le {n k : ℕ} (hn : 0 < n) (hk : Admissible n k) : k ≤ n := by
  rcases hk with ⟨A, hA, hpoints⟩
  have hpos : 0 < A.card := by
    rw [hA]
    exact hn
  have hnonempty : A.Nonempty := Finset.card_pos.mp hpos
  rcases hnonempty with ⟨x, hx⟩
  rcases hpoints x hx with ⟨d, hd⟩
  calc
    k ≤ equidistantCount A x d := hd
    _ ≤ A.card := by
      unfold equidistantCount
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := hA

/-- The admissibility set used by `f n` is bounded above for every positive `n`;
this is the required boundedness control for the `sSup` definition. -/
theorem admissible_bddAbove {n : ℕ} (hn : 0 < n) :
    BddAbove {k : ℕ | Admissible n k} := by
  refine ⟨n, ?_⟩
  intro k hk
  exact admissible_le hn hk

/-- A singleton is an explicit non-vacuous control: zero equidistant neighbours
are possible, while one equidistant neighbour is impossible. -/
theorem singleton_control :
    Admissible 1 0 ∧ ¬ Admissible 1 1 := by
  constructor
  · refine ⟨{0}, by simp, ?_⟩
    intro x hx
    refine ⟨1, ?_⟩
    simp [equidistantCount]
  · intro h
    rcases h with ⟨A, hA, hpoints⟩
    rcases Finset.card_eq_one.mp hA with ⟨a, ha⟩
    subst A
    have hx : a ∈ ({a} : Finset Plane) := by simp
    rcases hpoints a hx with ⟨d, hd⟩
    simp [equidistantCount] at hd

/-- For every positive `n`, zero is admissible.  This records the nonemptiness
needed by the `sSup` definition; constructing an arbitrary `n`-point set in
Euclidean four-space is left as an explicit formalization gap. -/
theorem admissible_nonempty {n : ℕ} (hn : 0 < n) :
    Set.Nonempty {k : ℕ | Admissible n k} := by
  sorry

/-- The source's question, formalized by reading `O(1)` as a uniform additive
constant in the natural-number inequality. -/
def Question : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, f n ≤ n / 2 + C

/-- The recorded resolution establishes the affirmative answer to the source's
question.  The substantial geometric argument of Avis--Erdős--Pach and
Swanepoel remains an external mathematical input here. -/
theorem answer : Question := by
  sorry Erdos754
