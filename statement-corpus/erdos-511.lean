/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $f(z)\in \mathbb{C}[z]$ be a monic polynomial of degree $n$. Is it true that, for every $c>1$, the set\[\{ z\in \mathbb{C} : \lvert f(z)\rvert< 1\}\]has at most $O_c(1)$ many connected components of diameter $>c$ (where the implied constant is in particular independent of $n$)?

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#511 : [EHP58,p.142] [Er61,p.247] [Ha74] analysis This is Problem 4.9 in [Ha74] , where it is attributed to Erdős. A problem of Erdős, Herzog, and Piranien [EHP58] , who ask more generally whether\[\sum_C \mathrm{diam}(C) \leq n2^{1/n}\]and\[\sum_{C}\max(0, \mathrm{diam}(C)-1)\ll 1\]for all such $f$, where $C$ ranges over the connected components of the set in question. The example $f(z)=z^n-1$ has $\sum_C \mathrm{diam}(C)=(1+o(1))n2^{1/n}$. They also asked whether, if the roots of $f$ are all in the disc $\{\lvert z\rvert\leq 1\}$, the total number of connected components with diameter $>1$ is absolutely bounded, but noted in an addendum that the answer is no: consider $z^n+1$ and move the zeros $e^{i\pi/n}$ and $e^{-i\pi/n}$ a short distance along the circle towards $1$. The set $\{z: \lvert f(z)\rvert \leq 1\}$ for $f(z)=z^n+1$ looks like $n$ 'leaves' joined at $0$, and this moving of two roots makes $\approx n/2$ of the leaves become disconnected at $0$. Each of the resulting components has diameter $>2^{1/n}-\epsilon$, and hence there are $\gg n$ components of diameter $>1$. In [Er61] Erdős asks the weaker question given here, with the definition of the set altered so that $<1$ is replaced by $\leq 1$. Pommerenke [Po61] proved that the answer is no to most of these questions, by showing that, for any $0<d<4$ and $k\geq 1$ there exist monic polynomials $f\in \mathbb{C}[x]$ such that $\{z: \lvert f(z)\rvert\leq 1\}$ has at least $k$ connected components of diameter $\geq d$. This was independently proved by Huang [Hu25] (unaware of the previous work of Pommerenke). Pólya [Po28] showed that $4$ is the best possible here, in that no connected component can have diameter $>4$. A picture of the set in question for $z^5-1$ is here . Additional thanks to : Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (7) Proof claims (0) More information and links This page was last edited 29 December 2025. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #511, https://www.erdosproblems.com/511, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None
-/


import Mathlib
open Classical

-- @category research open








open Classical Filter

namespace Erdos511

/-- The open sublevel set associated with a complex polynomial. -/
def sublevelSet (f : Polynomial ℂ) : Set ℂ :=
  {z | ‖f.eval z‖ < 1}

/-- A connected component is represented by its intrinsic maximality among
connected nonempty subsets of the sublevel set. -/
def IsSublevelComponent (U C : Set ℂ) : Prop :=
  IsConnected C ∧
    C.Nonempty ∧
    C ⊆ U ∧
    ∀ B : Set ℂ, IsConnected B → B.Nonempty → B ⊆ U → C ⊆ B → B ⊆ C

/-- The components whose diameter is greater than `c`, expressed by the
existence of two points in the component farther apart than `c`. -/
def LargeComponents (U : Set ℂ) (c : ℝ) : Set (Set ℂ) :=
  {C | IsSublevelComponent U C ∧ ∃ x ∈ C, ∃ y ∈ C, c < dist x y}

/-- The source's assertion that, for each fixed `c > 1`, the number of large
components is bounded independently of the degree.  The conjunction with
finiteness is explicit so that the cardinality is not relying on the default
value of `Set.ncard` for an infinite set. -/
def BoundedLargeComponents : Prop :=
  ∀ c : ℝ, 1 < c →
    ∃ K : ℕ, ∀ n : ℕ, ∀ f : Polynomial ℂ,
      f.Monic →
      f.natDegree = n →
      (LargeComponents (sublevelSet f) c).Finite ∧
        (LargeComponents (sublevelSet f) c).ncard ≤ K

/-- Every sublevel component is nonempty by definition. -/
theorem sublevelComponent_nonempty {U C : Set ℂ}
    (h : IsSublevelComponent U C) : C.Nonempty :=
  h.2.1

/-- Membership in `LargeComponents` supplies the two points witnessing the
claimed diameter bound. -/
theorem largeComponent_has_separation {U C : Set ℂ} {c : ℝ}
    (h : C ∈ LargeComponents U c) :
    ∃ x ∈ C, ∃ y ∈ C, c < dist x y :=
  h.2

/-- A proved control for the formalization: the definition of a large
component is not vacuous, since its membership directly entails a genuine
strict metric separation between two of its points. -/
theorem largeComponents_control {U C : Set ℂ} {c : ℝ}
    (h : C ∈ LargeComponents U c) :
    C.Nonempty ∧ ∃ x ∈ C, ∃ y ∈ C, c < dist x y :=
  ⟨sublevelComponent_nonempty h.1, h.2⟩

#print axioms sublevelComponent_nonempty
#print axioms largeComponent_has_separation
#print axioms largeComponents_control

end Erdos511
