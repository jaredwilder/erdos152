/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
If $A=\{z_1,z_2,\ldots \}\in \mathbb{R}^2$ is an infinite sequence then let\[f(r)=\max_C \left\lvert \lvert A\cap C\rvert-\pi r^2\right\rvert,\]where the maximum is taken over all circles $C$ of radius $r$. Is $f(r)$ unbounded for every $A$? How fast does $f(r)$ grow?
    
NODE n001-resolution (resolution), VERBATIM:
#989 : [Er64b] discrepancy This was settled by Beck [Be87] , who proved that\[f(r) \gg r^{1/2}\]for all $A$, and there exists $A$ such that\[f(r) \ll (r\log r)^{1/2}.\] Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #989, https://www.erdosproblems.com/989, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/






import Mathlib
open Classical
open scoped BigOperators

-- @category research solved







open Classical Filter

namespace Erdos989

/-- A circle in the Euclidean plane, represented by its centre and radius. -/
structure CircleData where
  center : EuclideanSpace ℝ (Fin 2)
  radius : ℝ

/-- Membership in a Euclidean circle viewed as its closed disk. -/
def InCircle (x : EuclideanSpace ℝ (Fin 2)) (C : CircleData) : Prop :=
  dist x C.center ≤ C.radius

/-- The number of points of a set lying in a given circle.

For an arbitrary infinite set this uses `Set.ncard`; consequently, the intended
finite-intersection interpretation requires the relevant intersections to be finite. -/
noncomputable def circleCount (A : Set (EuclideanSpace ℝ (Fin 2))) (C : CircleData) : ℕ :=
  Set.ncard {x : EuclideanSpace ℝ (Fin 2) | x ∈ A ∧ InCircle x C}

/-- The discrepancy of a set in one circle of radius `r`. -/
noncomputable def circleDiscrepancy
    (A : Set (EuclideanSpace ℝ (Fin 2))) (C : CircleData) : ℝ :=
  |(circleCount A C : ℝ) - Real.pi * C.radius ^ 2|

/-- The supremal version of the source's function, with circles of radius `r`.

The source writes a maximum. This formalization uses `sSup`, since the family of
all centres is not finite. The intended mathematical use additionally requires
the displayed set to be nonempty and bounded above; those facts are not hidden
in the definition. -/
noncomputable def discrepancy
    (A : Set (EuclideanSpace ℝ (Fin 2))) (r : ℝ) : ℝ :=
  sSup {d : ℝ | ∃ C : CircleData, C.radius = r ∧ d = circleDiscrepancy A C}

/-- CONTROL: the circle count of the empty set is genuinely computed. -/
theorem circleCount_empty (C : CircleData) :
    circleCount (∅ : Set (EuclideanSpace ℝ (Fin 2))) C = 0 := by
  simp [circleCount]

/-- A decidable lattice model of containment in a disk, used for finite witnesses. -/
def LatticeInDisk (p c : Fin 2 → ℤ) (r : ℕ) : Prop :=
  ∑ i, (p i - c i) ^ 2 ≤ (r : ℤ) ^ 2

/-- A finite lattice configuration is covered by one disk. -/
def CoversLatticeDisk {n : ℕ}
    (A : Fin n → Fin 2 → ℤ) (c : Fin 2 → ℤ) (r : ℕ) : Prop :=
  ∀ i, LatticeInDisk (A i) c r

/-- POSITIVE WITNESS: three coincident lattice points are covered by the
radius-zero disk centred at the origin. -/
theorem CoversLatticeDisk_witness_pos :
    CoversLatticeDisk (fun _ : Fin 3 => fun _ : Fin 2 => (0 : ℤ))
      (fun _ : Fin 2 => (0 : ℤ)) 0 := by
  decide

/-- NEGATIVE WITNESS: the positive configuration with exactly one point moved
one lattice unit away, so the radius-zero cover fails at exactly that point. -/
theorem CoversLatticeDisk_witness_neg :
    ¬ CoversLatticeDisk
      (fun i : Fin 3 =>
        if i = (2 : Fin 3) then
          (fun j : Fin 2 => if j = (0 : Fin 2) then (1 : ℤ) else 0)
        else
          (fun _ : Fin 2 => (0 : ℤ)))
      (fun _ : Fin 2 => (0 : ℤ)) 0 := by
  decide

/-- Beck's settled resolution, formalized with the source's asymptotic
comparisons as explicit eventual inequalities.

SOURCE MAPPING: the source defines `f(r)` as the maximum discrepancy over all
circles of radius `r`; the lower assertion `f(r) ≫ r^{1/2}` means that some
positive constant times `sqrt r` is eventually below `f(r)`, while the upper
assertion `f(r) ≪ (r log r)^{1/2}` means that some constant times that quantity
eventually bounds `f(r)` above. The source does not state the finiteness and
local-finiteness hypotheses needed to make `Set.ncard` and the supremum model
fully faithful, so the derivation from those definitions remains an explicit
gap. -/
theorem beck_resolution :
    (∀ A : Set (EuclideanSpace ℝ (Fin 2)),
      A.Infinite →
        ∃ c : ℝ, 0 < c ∧
          ∀ᶠ r : ℝ in atTop, c * Real.sqrt r ≤ discrepancy A r) ∧
    ∃ A : Set (EuclideanSpace ℝ (Fin 2)), A.Infinite ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ᶠ r : ℝ in atTop,
          discrepancy A r ≤ C * Real.sqrt (r * Real.log r) := by
  sorry Erdos989
