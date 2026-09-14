/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $A=\{n_1<n_2<\cdots\}\subset \mathbb{N}$ be a lacunary sequence (so there exists some $\epsilon>0$ with $n_{k+1}\geq (1+\epsilon)n_k$ for all $k$). Is it true that there must exist a finite colouring of $\mathbb{N}$ with no monochromatic solutions to $a-b\in A$?

NODE n001-resolution (resolution), VERBATIM:
#894 : [Ka01] number theory | ramsey theory Asked by Erdős in 1987, according to Katznelson [Ka01] . In other words, does the Cayley graph defined on $\mathbb{Z}$ by a lacunary sequence have a finite chromatic number? Katznelson observed that a positive solution to the problem follows from the answer to [464] , which yields an irrational $\theta$ and $\delta>0$ such that $\inf_k \| \theta n_k\|>\delta$. Indeed, given such a $\theta$ a colouring of $\mathbb{N}$ using $\ll \delta^{-1}$ colours lacking any solution to $a-b\in A$ can be produced by dividing $\mathbb{R}/\mathbb{Z}$ into disjoint intervals of length $\leq \delta$ and then colouring $n$ according to which interval $\| \theta n\|$ belongs to. In particular, the solution to [464] implies the answer to this question is yes, with the best known quantitative bound, due to Peres and Schlag [PeSc10] , being that there is a colouring with no solutions using at most\[\ll \epsilon^{-1}\log(1/\epsilon)\]colours. Additional thanks to : Euro Vidal Sampaio Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #894, https://www.erdosproblems.com/894, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research open








open Classical Filter

namespace Erdos894

/-- A finite, decidable model of the source's lacunarity condition, using the
    concrete ratio bound `2`, corresponding to the special case `ε = 1`. -/
def LacunaryBounded (n : ℕ) (s : Fin n → ℕ) : Prop :=
  StrictMono s ∧ ∀ i : Fin (n - 1), 2 * s i.castSucc ≤ s i.succ

/-- POSITIVE WITNESS: the sequence `1, 2, 4` is increasing and satisfies the
    finite ratio-two lacunarity condition. -/
theorem LacunaryBounded_witness_pos :
    LacunaryBounded 3 (fun i : Fin 3 =>
      if i.val = 0 then 1 else if i.val = 1 then 2 else 4) := by
  decide

/-- NEGATIVE WITNESS: the near miss `1, 2, 3` is increasing, but fails exactly
    the second ratio-two inequality. -/
theorem LacunaryBounded_witness_neg :
    ¬ LacunaryBounded 3 (fun i : Fin 3 =>
      if i.val = 0 then 1 else if i.val = 1 then 2 else 3) := by
  decide

/-- `AvoidsBounded N m q s c` means that `c` is a `q`-colouring of the first
    `N` natural numbers with no monochromatic positive difference belonging to
    the finite sequence `s`. The first two arguments in the difference are
    the larger and smaller vertices, respectively. -/
def AvoidsBounded (N m q : ℕ) (s : Fin m → ℕ) (c : Fin N → Fin q) : Prop :=
  ∀ x y k, y.val < x.val → x.val - y.val = s k → c x ≠ c y

/-- POSITIVE WITNESS: alternating two colours avoid the difference `1` on
    the finite interval `0, 1, 2`. -/
theorem AvoidsBounded_witness_pos :
    AvoidsBounded 3 1 2 (fun _ : Fin 1 => 1)
      (fun x : Fin 3 => if x.val = 1 then (1 : Fin 2) else 0) := by
  decide

/-- NEGATIVE WITNESS: the one-colour constant colouring is a near miss for
    the preceding example and fails on the single edge of difference `1`. -/
theorem AvoidsBounded_witness_neg :
    ¬ AvoidsBounded 3 1 1 (fun _ : Fin 1 => 1)
      (fun _ : Fin 3 => (0 : Fin 1)) := by
  decide

/-- The bounded finite analogue of the question: there exists a colouring of
    the first `N` naturals with `q` colours avoiding all differences in `s`. -/
def BoundedQuestion (N m q : ℕ) (s : Fin m → ℕ) : Prop :=
  ∃ c : Fin N → Fin q, AvoidsBounded N m q s c

/-- POSITIVE WITNESS: the finite question holds for the difference set
    consisting of `1`, on three vertices with two colours. -/
theorem BoundedQuestion_witness_pos :
    BoundedQuestion 3 1 2 (fun _ : Fin 1 => 1) := by
  exact ⟨fun x : Fin 3 => if x.val = 1 then (1 : Fin 2) else 0, by decide⟩

/-- NEGATIVE WITNESS: reducing the number of colours to one is a near miss
    which makes the same finite avoidance question false. -/
theorem BoundedQuestion_witness_neg :
    ¬ BoundedQuestion 3 1 1 (fun _ : Fin 1 => 1) := by
  decide

/-- The source question formalized literally: every strictly increasing
    lacunary sequence of natural numbers admits a finite colouring with no
    monochromatic solution to `a - b ∈ A`. This is recorded as a proposition,
    rather than asserted here as a theorem, because the source presents the
    positive answer through the separate result [464]. -/
def Question : Prop :=
  ∀ s : ℕ → ℕ,
    StrictMono s →
      (∃ ε : ℝ, 0 < ε ∧
        ∀ k : ℕ, (1 + ε) * (s k : ℝ) ≤ (s (k + 1) : ℝ)) →
        ∃ q : ℕ, ∃ c : ℕ → Fin q,
          ∀ x y k, y < x → x - y = s k → c x ≠ c y

#print axioms LacunaryBounded_witness_pos
#print axioms LacunaryBounded_witness_neg
#print axioms AvoidsBounded_witness_pos
#print axioms AvoidsBounded_witness_neg
#print axioms BoundedQuestion_witness_pos
#print axioms BoundedQuestion_witness_neg

end Erdos894
