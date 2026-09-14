/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $n\geq 2$. Is there a space $S$ of dimension $n$ such that $S^2$ also has dimension $n$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#909 : [Er82e] analysis | topology The space of rational points in Hilbert space has this property for $n=1$. This was proved for general $n$ by Anderson and Keisler [AnKe67] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #909, https://www.erdosproblems.com/909, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on mdelvecchio Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos909

/-- 
A placeholder for covering dimension of a topological space. Mathlib does not provide the
general topological-dimension construction needed by the source entry, so this definition is
left as an explicit honest gap rather than replacing topological dimension by an unrelated
invariant.
-/
noncomputable def topologicalDimension (S : Type) (t : TopologicalSpace S) : Nat := by
  sorry

/-- 
The dimension assigned to the Cartesian square of `S`, using the product topology. Here
`S²` is formalized as the genuine product type `S × S`.
-/
noncomputable def squareDimension (S : Type) (t : TopologicalSpace S) : Nat :=
  let _ := t
  topologicalDimension (S × S) inferInstance

/-- 
`HasSquareDimension n` means that there is a topological space `S` whose dimension and the
dimension of its Cartesian square are both `n`. The source uses topological dimension; the
underlying dimension function remains an explicit named gap above.
-/
def HasSquareDimension (n : Nat) : Prop :=
  ∃ (S : Type) (t : TopologicalSpace S),
    topologicalDimension S t = n ∧ squareDimension S t = n

/-- 
The question from the source, read word by word: for every `n` with `2 ≤ n`, there exists a
topological space of dimension `n` whose Cartesian square also has dimension `n`.
-/
def Question : Prop :=
  ∀ n : Nat, 2 ≤ n → HasSquareDimension n

/-- 
A finite decidable control encoding one candidate dimension and one candidate square dimension.
This is only a bounded sanity check for the equality conditions; it is not being presented as
a replacement for the source's topological existence statement.
-/
def BoundedDimensionCheck (n d e : Nat) : Prop :=
  2 ≤ n ∧ d = n ∧ e = n

/-- POSITIVE WITNESS: both candidate dimensions equal the required dimension. -/
theorem BoundedDimensionCheck_witness_pos :
    BoundedDimensionCheck 2 2 2 := by
  decide

/-- NEGATIVE WITNESS: a near miss changing only the dimension of the original space. -/
theorem BoundedDimensionCheck_witness_neg :
    ¬ BoundedDimensionCheck 2 1 2 := by
  decide

/-- 
The Anderson--Keisler resolution recorded by the source. Its proof requires the missing
general theory of topological dimension and the cited construction, so the remaining
mathematical step is deliberately marked as an honest gap.
-/
theorem anderson_keisler_resolution : Question := by
  sorry Erdos909
