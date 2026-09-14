/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $n\geq 1$ and\[A=\{a_1<\cdots <a_{\phi(n)}\}=\{ 1\leq m<n : (m,n)=1\}.\]Is it true that\[ \sum_{1\leq k<\phi(n)}(a_{k+1}-a_k)^2 \ll \frac{n^2}{\phi(n)}?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#220 : [Er40,p.440] [Er55c,p.2] [Er57,p.292] [Er61,p.224] [Er65b,p.206] [Er73,p.135] [Er79,p.70] [ErGr80,p.89] [Er81k,p.3] [Er85c,p.80] number theory The answer is yes, as proved by Montgomery and Vaughan [MoVa86] , who in fact proved that for any $\gamma\geq 1$\[ \sum_{1\leq k<\phi(n)}(a_{k+1}-a_k)^\gamma \ll \frac{n^\gamma}{\phi(n)^{\gamma-1}}.\]This general form was also asked by Erdős in [Er73] . This is discussed in problem B40 of Guy's collection [Gu04] . Additional thanks to : Stijn Cambie and Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (3) Proof claims (0) More information and links This page was last edited 08 December 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #220, https://www.erdosproblems.com/220, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A322144 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

import Mathlib

-- @category research solved

namespace Erdos220

/-- The increasing list of integers in the interval `1 ≤ m < n` that are
coprime to `n`, formalizing the set `A` in the source. -/
def admissibleList (n : ℕ) : List ℕ :=
  (Finset.filter (fun m => 1 ≤ m ∧ Nat.Coprime m n) (Finset.range n)).sort
    (fun a b => a ≤ b)

/-- The successive gaps in the increasing list of reduced residues modulo `n`. -/
def residueGaps (n : ℕ) : List ℕ :=
  List.zipWith (fun x y => x - y)
    (admissibleList n).drop 1
    (admissibleList n).take ((admissibleList n).length - 1)

/-- The real `γ`-moment of the successive gaps.  The use of real `γ` follows
the general form recorded in the resolution. -/
def gapMoment (n : ℕ) (γ : ℝ) : ℝ :=
  ((residueGaps n).map (fun d => Real.rpow (d : ℝ) γ)).sum

/-- The general Montgomery--Vaughan bound recorded in the resolution, with
the implied constant allowed to depend on `γ`. -/
def GeneralBound : Prop :=
  ∀ γ : ℝ, 1 ≤ γ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, 1 ≤ n →
        gapMoment n γ ≤
          C * Real.rpow (n : ℝ) γ /
            Real.rpow (Nat.totient n : ℝ) (γ - 1)

/-- The quadratic question from the source, expressed using the preceding
definition and the totient `Nat.totient`. -/
def QuadraticBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, 1 ≤ n →
      gapMoment n 2 ≤
        C * Real.rpow (n : ℝ) 2 /
          Real.rpow (Nat.totient n : ℝ) 1

/-- The endpoint `n = 1` has no successive reduced-residue gaps, so its gap
moment is exactly zero.  This is a proved control fact for the definitions
used in the formalization. -/
theorem gapMoment_one (γ : ℝ) : gapMoment 1 γ = 0 := by
  simp [gapMoment, residueGaps, admissibleList]

#print axioms gapMoment_one

end Erdos220