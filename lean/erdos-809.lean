import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-- A graph on `Fin n`, represented by a Boolean adjacency relation. -/
def GraphOn (n : ℕ) := Fin n → Fin n → Bool

/-- The successor in the cyclic index set `Fin l`. -/
def cycleNext (l : ℕ) (i : Fin l) : Fin l :=
  ⟨(i.val + 1) % l, by
    have hi : i.val < l := i.isLt
    have hl : 0 < l := by omega
    exact Nat.mod_lt _ hl⟩

/-- There is an `r`-colouring of an `n`-vertex, `e`-edge graph
    in which every copy of `C_l` is rainbow. -/
def AntiRamseyFeasible (n e l r : ℕ) : Prop :=
  ∃ G : GraphOn n, ∃ c : Fin n → Fin n → Fin r,
    (∀ i j, G i j = G j i) ∧
    (∀ i, G i i = false) ∧
    ((Finset.univ.filter
        (fun p : Fin n × Fin n =>
          p.1 < p.2 ∧ G p.1 p.2 = true)).card = e) ∧
    (∀ i j, c i j = c j i) ∧
    (∀ f : Fin l → Fin n,
      Function.Injective f →
      (∀ i : Fin l, G (f i) (f (cycleNext l i)) = true) →
      ∀ i j : Fin l, i ≠ j →
        c (f i) (f (cycleNext l i)) ≠
          c (f j) (f (cycleNext l j)))

/-- The smallest number of colours with the required property. -/
noncomputable def chiS (n e l : ℕ) : ℕ :=
  if h : ∃ r : ℕ, AntiRamseyFeasible n e l r then
    Nat.find h
  else
    0

/-- A small instance where the feasibility predicate holds. -/
theorem witness_pos : AntiRamseyFeasible 1 0 3 1 := by
  refine ⟨(fun _ _ => false), (fun _ _ => 0), ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · simp
  · intro f hf i j hij
    have hf01 : f (0 : Fin 3) = f (1 : Fin 3) := Subsingleton.elim _ _
    have hEq : (0 : Fin 3) = 1 := hf hf01
    have hne : (0 : Fin 3) ≠ 1 := by decide
    exact (hne hEq).elim

/-- A small instance where the feasibility predicate fails. -/
theorem witness_neg : ¬ AntiRamseyFeasible 1 0 3 0 := by
  rintro ⟨G, c, h⟩
  exact Fin.elim0 (c (0 : Fin 1) (0 : Fin 1))

/-- The anti-Ramsey asymptotic question from Erdos problem 809. -/
theorem erdos_problem_809 :
    ∀ k : ℕ, 3 ≤ k →
      Asymptotics.IsEquivalent atTop
        (fun n : ℕ =>
          (chiS n (n ^ 2 / 4 + 1) (2 * k + 1) : ℝ))
        (fun n : ℕ => (n : ℝ) ^ 2 / 8) := by
  sorry

end