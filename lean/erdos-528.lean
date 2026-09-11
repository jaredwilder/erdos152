import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators
open Filter
open scoped Topology

/-!
Question n000-question (question), verbatim in mathematical content:

Let f(n,k) count the number of self-avoiding walks of n steps (beginning at the
origin) in Z^k (i.e. those walks which do not intersect themselves). Determine
C_k = lim_{n→∞} f(n,k)^(1/n).

Resolution n001-resolution:

#528 : [Er61,p.254] geometry. The constant C_k is sometimes known as the
connective constant. Hammersley and Morton [HM54] showed that this limit exists,
and it is trivial that k ≤ C_k ≤ 2k-1. Kesten [Ke63] proved that
C_k = 2k-1-1/2k+O(1/k^2), and more precise asymptotics are given by Clisby,
Liang, and Slade [CLS07]. Conway and Guttmann [CG93] showed that C_2 ≥ 2.62
and Alm [Al93] showed that C_2 ≤ 2.696. Jacobsen, Scullard, and Guttmann
[JSG16] have computed the first few decimal places of C_2, showing that
C_2 = 2.6381585303279⋯. See also [529].
-/

/-- A lattice step in `ℤ^k`: a coordinate and a choice of sign. -/
abbrev Direction (k : ℕ) := Fin k × Bool

/-- The displacement contributed by one lattice step in one coordinate. -/
def step (d : Direction k) (j : Fin k) : ℤ :=
  if d.1 = j then
    if d.2 then 1 else -1
  else
    0

/-- The position after `t` steps of a walk of length `n`. -/
def position (k n : ℕ) (w : Fin n → Direction k)
    (t : Fin (n + 1)) : Fin k → ℤ :=
  let h : t.val ≤ n := Nat.le_of_lt_succ t.isLt
  fun j =>
    ∑ i : Fin t, step (w ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩) j

/-- A walk is self-avoiding when all of its visited lattice sites are distinct. -/
def selfAvoiding (k n : ℕ) (w : Fin n → Direction k) : Prop :=
  ∀ i j : Fin (n + 1), i ≠ j → position k n w i ≠ position k n w j

/-- The number of self-avoiding walks of `n` steps in `ℤ^k`. -/
def f (n k : ℕ) : ℕ :=
  (Finset.univ.filter (selfAvoiding k n)).card

/-- The connective-constant assertion, including the bounds recorded in the source. -/
def ConnectiveConstant (k : ℕ) (C : ℝ) : Prop :=
  0 < k ∧
    Filter.Tendsto
      (fun n : ℕ => Real.rpow (f n k : ℝ) (1 / (n : ℝ)))
      atTop (𝓝 C) ∧
    (k : ℝ) ≤ C ∧ C ≤ 2 * (k : ℝ) - 1

/-- A one-step walk in one dimension which moves to the right is self-avoiding. -/
theorem witness_pos :
    selfAvoiding 1 1 (fun _ : Fin 1 => ((0 : Fin 1), true)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · intro heq
    have hh := congrFun heq (0 : Fin 1)
    norm_num [position, step, Fin.sum_univ_succ] at hh
  · intro heq
    have hh := congrFun heq (0 : Fin 1)
    norm_num [position, step, Fin.sum_univ_succ] at hh
  · exact (hij rfl).elim

/-- Moving right and then left revisits the origin, so this walk is not self-avoiding. -/
theorem witness_neg :
    ¬ selfAvoiding 1 2
      (fun i : Fin 2 =>
        if i = 0 then ((0 : Fin 1), true) else ((0 : Fin 1), false)) := by
  intro h
  have h' := h (0 : Fin 3) (2 : Fin 3) (by decide)
  apply h'
  funext j
  fin_cases j
  native_decide

/-- Formal statement of the connective-constant result described in Erdos problem 528. -/
theorem erdos_problem_528 :
    ∀ k : ℕ, 0 < k → ∃ C : ℝ, ConnectiveConstant k C := by
  sorry

end