import Mathlib

-- @category research solved

/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $A\subset \mathbb{R}^2$ be a set of $n$ points such that any subset of size $4$ determines at least $5$ distinct distances. Must $A$ determine $\gg n^2$ many distances?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#135 : [Er97b,p.231] [Er97e,p.531] distances | geometry A problem of Erdős and Gyárfás. Erdős could not even prove that the number of distances is at least $f(n)n$ where $f(n)\to \infty$. Erdős [Er97b] also makes the even stronger conjecture that $A$ must contain $\gg n$ many points such that all pairwise distances are distinct. Answered in the negative by Tao [Ta24c] , who proved that for any large $n$ there exists a set of $n$ points in $\mathbb{R}^2$ such that any four points determine at least five distinct distances, yet there are $\ll n^2/\sqrt{\log n}$ distinct distances in total. Tao discusses his solution in a blog post . More generally, one can ask how many distances $A$ must determine if every set of $p$ points determines at least $q$ distances. See also [136] , [657] , and [659] . Additional thanks to : Sarosh Adenwalla and Desmond Weisenberg Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 16 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #135, https://www.erdosproblems.com/135, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

namespace Erdos135

/-- The finite set of unordered pairs of distinct indices in `Fin n`. -/
def pointPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

/-- The set of Euclidean distances determined by an indexed family of points. -/
noncomputable def distanceValues (n : ℕ)
    (A : Fin n → EuclideanSpace ℝ (Fin 2)) : Finset ℝ :=
  (pointPairs n).image (fun p => dist (A p.1) (A p.2))

/-- The number of distinct Euclidean distances determined by `A`. -/
noncomputable def distanceCount (n : ℕ)
    (A : Fin n → EuclideanSpace ℝ (Fin 2)) : ℕ :=
  (distanceValues n A).card

/-- The number of distinct distances among the six pairs selected by four indexed points. -/
noncomputable def fourDistanceCount (n : ℕ)
    (A : Fin n → EuclideanSpace ℝ (Fin 2))
    (e : Fin 4 → Fin n) : ℕ :=
  ((pointPairs 4).image
      (fun p => dist (A (e p.1)) (A (e p.2)))).card

/-- Every injectively selected set of four points determines at least five distances. -/
def HasFiveDistancesOnFour
    (n : ℕ) (A : Fin n → EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∀ e : Fin 4 → Fin n, Function.Injective e →
    5 ≤ fourDistanceCount n A e

/-- A quadratic lower bound for the number of distances, uniformly for all sufficiently
large finite point sets satisfying the four-point hypothesis. -/
def QuadraticDistanceConclusion : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ A : Fin n → EuclideanSpace ℝ (Fin 2),
      Function.Injective A →
      HasFiveDistancesOnFour n A →
      c * (n : ℝ) ^ 2 ≤ (distanceCount n A : ℝ)

/-- The literal formalization of the question: whether every sufficiently large admissible
configuration has quadratically many distinct distances. -/
def Question : Prop :=
  QuadraticDistanceConclusion

/-- A formal version of the counterexample shape recorded in the resolution: for all
sufficiently large `n`, an admissible configuration has at most a constant multiple of
`n² / sqrt(log n)` distances. -/
def TaoCounterexample : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ A : Fin n → EuclideanSpace ℝ (Fin 2),
      Function.Injective A ∧
      HasFiveDistancesOnFour n A ∧
      (distanceCount n A : ℝ) ≤
        C * (n : ℝ) ^ 2 / Real.sqrt (Nat.log 2 n : ℝ)

/-- The resolution records that the quadratic conclusion is answered negatively by Tao's
construction; this declaration records that known result as a proposition rather than
silently presenting it as a proved theorem in this file. -/
def SourceResolution : Prop :=
  ¬ Question ∧ TaoCounterexample

/-- Any four selected points determine at most the six pairwise distances available among
four points. -/
lemma fourDistanceCount_le_six
    (n : ℕ) (A : Fin n → EuclideanSpace ℝ (Fin 2))
    (e : Fin 4 → Fin n) :
    fourDistanceCount n A e ≤ 6 := by
  unfold fourDistanceCount
  calc
    ((pointPairs 4).image
        (fun p => dist (A (e p.1)) (A (e p.2)))).card ≤
        (pointPairs 4).card := Finset.card_image_le
    _ ≤ 6 := by decide

#print axioms fourDistanceCount_le_six

end Erdos135