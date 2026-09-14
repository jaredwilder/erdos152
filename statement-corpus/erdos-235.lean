/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $N_k=2\cdot 3\cdots p_k$ and $\{a_1<a_2<\cdots <a_{\phi(N_k)}\}$ be the integers $<N_k$ which are relatively prime to $N_k$. Then, for any $c\geq 0$, the limit\[\frac{\#\{ a_i-a_{i-1}\leq c \frac{N_k}{\phi(N_k)} : 2\leq i\leq \phi(N_k)\}}{\phi(N_k)}\]exists and is a continuous function of $c$.
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#235 : [Er55c] number theory Solved by Hooley [Ho65] , who proved that these gaps have an exponential distribution: that is, if $f(c)$ is the function in question, then\[f(c)=(1+o(1))(1-e^{-c})\](where the $o(1)$ goes to $0 uniformly as $k\to \infty$). See also [234] for a more difficult version of this problem using actual primes. Additional thanks to : Dogmachine and Ofir Gorodetsky Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 22 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #235, https://www.erdosproblems.com/235, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos235

/-- The product of the first `k` primes, with the empty product at `k = 0`. -/
noncomputable def primorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- The integers below the primorial that are relatively prime to it. -/
noncomputable def reducedResidues (k : ℕ) : Finset ℕ :=
  (Finset.range (primorial k)).filter
    (fun a => Nat.Coprime a (primorial k))

/-- The normalized count of adjacent reduced-residue gaps at most
`c * N_k / φ(N_k)`.  The list is sorted increasingly, so its adjacent
pairs represent the gaps in the source statement. -/
noncomputable def gapProportion (k : ℕ) (c : ℝ) : ℝ :=
  let xs := (reducedResidues k).sort (· ≤ ·)
  let js := Finset.Icc 1 (xs.length - 1)
  ((js.filter (fun i =>
      ((xs.get! i - xs.get! (i - 1) : ℕ) : ℝ) ≤
        c * (primorial k : ℝ) / (Nat.totient (primorial k) : ℝ))).card : ℝ) /
    (Nat.totient (primorial k) : ℝ)

/-- A basic sanity check: the empty primorial is one. -/
theorem primorial_zero : primorial 0 = 1 := by
  simp [primorial]

/-- A computed control showing that the reduced-residue construction is nontrivial:
for the empty primorial there is exactly one residue below one. -/
theorem reducedResidues_zero_card : (reducedResidues 0).card = 1 := by
  simp [reducedResidues, primorial]

/-- Hooley's exponential-distribution resolution, formalized as the convergence
of the gap proportions to `1 - exp (-c)` for every nonnegative `c`.
The proof of this analytic number-theoretic input remains to be supplied. -/
theorem hooley_resolution :
    ∀ c : ℝ, 0 ≤ c →
      Tendsto (fun k : ℕ => gapProportion k c) atTop
        (𝓝 (1 - Real.exp (-c))) := by
  sorry

/-- Formalization of Erdős problem #235.

The source says that there is a continuous function of `c` giving the limit of
the normalized adjacent-gap counts.  Hooley's resolution identifies that
function as `1 - exp (-c)` on the required range `c ≥ 0`; we extend this
formula to all real `c` only so that continuity has an ordinary global
statement. -/
theorem question :
    ∃ f : ℝ → ℝ,
      Continuous f ∧
      ∀ c : ℝ, 0 ≤ c →
        Tendsto (fun k : ℕ => gapProportion k c) atTop (𝓝 (f c)) := by
  refine ⟨fun c => 1 - Real.exp (-c), ?_, ?_⟩
  · fun_prop
  · intro c hc
    exact hooley_resolution c hc

#print axioms primorial_zero
#print axioms reducedResidues_zero_card
#print axioms question

end Erdos235
