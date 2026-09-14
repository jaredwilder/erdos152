/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $W(3,k)$ be the van der Waerden number defined as the minimum $n$ such that in any red/blue colouring of $\{1,\ldots,n\}$ there exists either a red $3$-term arithmetic progression or a blue $k$-term arithmetic progression. Give reasonable bounds for $W(3,k)$. In particular, give any non-trivial lower bounds for $W(3,k)$ and prove that $W(3,k) < \exp(k^c)$ for some constant $c<1$.
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#721 : [Er80,p.91] [Er81] number theory | additive combinatorics | ramsey theory While we do not have a full understanding of the growth of $W(3,k)$, both of the specific challenges of Erdős have been met. Green [Gr22] established the superpolynomial lower bound\[W(3,k) \geq \exp\left( c\frac{(\log k)^{4/3}}{(\log\log k) ^{1/3}}\right)\]for some constant $c>0$ (in particular disproving a conjecture of Graham that $W(3,k)\ll k^2$). Hunter [Hu22] improved this to\[W(3,k) \geq \exp\left( c\frac{(\log k)^{2}}{\log\log k}\right).\]The first to show that $W(3,k) < \exp(k^c)$ for some $c<1$ was Schoen [Sc21] . The best upper bound currently known is\[W(3,k) \ll \exp\left( O((\log k)^9)\right),\]which follows from the best bounds known for sets without three-term arithmetic progressions (see [BlSi23] which improves slightly on the bounds due to Kelley and Meka [KeMe23] ). Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 04 April 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #721, https://www.erdosproblems.com/721, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A171081 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research open







open Classical Filter

namespace Erdos721

/-- A monochromatic arithmetic progression of length `l` in a red/blue colouring
of `Fin n`, with colour `b`. The parameters `a` and `d` describe the progression
by the formula `a + i*d`. -/
def IsArithmeticProgression (c : Fin n → Bool) (l : Nat) (b : Bool) : Prop :=
  ∃ a d : Nat, 0 < d ∧
    ∀ i : Fin l,
      a + i.val * d < n ∧
        c ⟨a + i.val * d, (by assumption)⟩ = b

/-- The van der Waerden property at parameters `n` and `k`: every colouring of
`Fin n` has either a red three-term arithmetic progression or a blue
`k`-term arithmetic progression. -/
def HasWaerdenProperty (n k : Nat) : Prop :=
  ∀ c : Fin n → Bool,
    IsArithmeticProgression c 3 true ∨
      IsArithmeticProgression c k false

/-- The literal minimum definition of `W(3,k)` as an `sInf`. The `sInf` junk
value on an empty set is relevant here, so all uses of this definition should
be accompanied by nonemptiness of the set of valid lengths; boundedness below
is automatic because the ambient type is `Nat`. -/
noncomputable def vanDerWaerden (k : Nat) : Nat :=
  sInf {n : Nat | HasWaerdenProperty n k}

/-- The defining set for `W(3,k)` is bounded below. This is the harmless
boundedness part of the `sInf` well-definedness check. -/
theorem waerden_set_bddBelow (k : Nat) :
    BddBelow {n : Nat | HasWaerdenProperty n k} := by
  refine ⟨0, ?_⟩
  intro n hn
  omega

/-- The finite-van-der-Waerden theorem, stated in the form needed to certify
that the `sInf` defining `vanDerWaerden` is not junk. The proof of this
substantial combinatorial input remains to be formalized. -/
theorem waerden_set_nonempty (k : Nat) (hk : 1 ≤ k) :
    Set.Nonempty {n : Nat | HasWaerdenProperty n k} := by
  sorry

/-- A basic sanity check: no colouring of a singleton contains a
three-term arithmetic progression. -/
theorem no_three_ap_on_singleton (c : Fin 1 → Bool) (b : Bool) :
    ¬ IsArithmeticProgression c 3 b := by
  rintro ⟨a, d, hd, h⟩
  have h0 := (h ⟨0, by omega⟩).1
  have h1 := (h ⟨1, by omega⟩).1
  omega

/-- A basic sanity check exercising the arithmetic-progression predicate:
the constant-blue colouring of `Fin 2` contains a blue progression of length
two. -/
theorem constant_blue_control :
    IsArithmeticProgression (fun _ : Fin 2 => false) 2 false := by
  refine ⟨0, 1, by omega, ?_⟩
  intro i
  have hi : i.val < 2 := i.isLt
  constructor
  · omega
  · simp

/-- The stronger lower bound recorded in the resolution: for some positive
constant `c`, Hunter's estimate holds for all sufficiently large `k`.
The analytic and additive-combinatorial proof of this literature result
remains an explicit gap. -/
def HunterLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∃ K : Nat, 3 ≤ K ∧
      ∀ k : Nat, K ≤ k →
        Real.exp
            (c * (Real.log (k : ℝ)) ^ 2 /
              Real.log (Real.log (k : ℝ))) ≤
          (vanDerWaerden k : ℝ)

/-- The subexponential upper bound requested in the question and attributed
in the resolution to Schoen: there is a constant `c < 1` giving the bound
for all sufficiently large `k`. This is stated separately from the lower
bound because the source records the result but supplies no proof exposition. -/
def SchoenUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∃ K : Nat, 1 ≤ K ∧
      ∀ k : Nat, K ≤ k →
        (vanDerWaerden k : ℝ) <
          Real.exp (Real.rpow (k : ℝ) c)

/-- The resolution's known lower bound for `W(3,k)`. This declaration is a
sorried literature input, not a claim that the proof has been formalized. -/
theorem hunter_lower_bound : HunterLowerBound := by
  sorry

/-- The answer to the specifically requested upper-bound challenge. This
declaration records Schoen's settled result as an explicit hypothesis whose
proof remains to be formalized. -/
theorem schoen_upper_bound : SchoenUpperBound := by
  sorry

#print axioms no_three_ap_on_singleton
#print axioms constant_blue_control

end Erdos721
