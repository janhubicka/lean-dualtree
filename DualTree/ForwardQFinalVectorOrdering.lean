import DualTree.ForwardQFinalProjectionOrder
import DualTree.VectorSkew
import DualTree.DirectionalSupport

/-!
# Vector-complete local coordinate words force the length inequalities
# needed by the final Lemma 27 projected-root gluing

The mixed-product Ramsey step supplies an ACTUAL mixed variable word f
whose vector component carries a q-complete skew family. Its vector
axioms are not cosmetic: they compare ambient root lengths at the
SAME intrinsic level across sorted coordinates, and strictly separate
EVERY level r from the next level r+1 across all coordinates.

The previous theorem checks that a nondecreasing pair of local
tail lengths in increasing frontier coordinates is transported by
P_i to the corrected forward auxiliary order in the complete T.
Here we extract those inequalities from the executable
VectorSkew.vectorCompleteB invariant, then apply them to the
genuinely projected local support roots.

This is the missing connection between vector-complete inputs
and the actual candidate T' geometry. It is NOT a proof that
the entire joined support is m-complete skew: mixed comparisons
with retained roots, exact intrinsic ranks in the joined support,
branching cardinalities, and the final ambient fibre word f'
are further obligations.
-/

namespace DualTree.ForwardQFinalVectorOrdering

open ForwardSourceQTree
open ForwardQFinalRefinementRoots
open ForwardQFinalProjectionOrder

/-- If two local source support vertices lie at the same
intrinsic level r<q, the vector-complete mixed word forces
their ambient tail lengths into increasing coordinate order. -/
theorem local_lengths_le_of_equal_level
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i j : Index c)
    (hij : i < j)
    (r : Nat) (hr : r < q)
    (z w : BoundedNode b (k - (m + 1)))
    (hz : z.1 ∈ (f.vector.components i).toVariableWord.supportNodes)
    (hw : w.1 ∈ (f.vector.components j).toVariableWord.supportNodes)
    (hrz : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 = r)
    (hrw : SkewTree.heightAt
      (f.vector.components j).toVariableWord.supportNodes w.1 = r) :
    z.1.length ≤ w.1.length := by
  have hparts := f.vector.vector_complete
  simp only [VectorSkew.vectorCompleteB, Bool.and_eq_true] at hparts
  have hsame : VectorSkew.sameLevelOrderedB
      (fun i => (f.vector.components i).toVariableWord.supportNodes)
      q = true := by
    tauto
  unfold VectorSkew.sameLevelOrderedB at hsame
  have hi := (List.all_eq_true.mp hsame) i
    (DirectionalSupport.mem_allFin _ i)
  have hj := (List.all_eq_true.mp hi) j
    (DirectionalSupport.mem_allFin _ j)
  have hlevels : (List.range q).all (fun r =>
      (VectorSkew.levelNodes
        (f.vector.components i).toVariableWord.supportNodes r).all
        (fun a =>
          (VectorSkew.levelNodes
            (f.vector.components j).toVariableWord.supportNodes r).all
              (fun d => decide (a.length ≤ d.length)))) = true := by
    simpa [hij] using hj
  have hrow :=
    (List.all_eq_true.mp hlevels) r (List.mem_range.mpr hr)
  have hzLevel :
      z.1 ∈ VectorSkew.levelNodes
        (f.vector.components i).toVariableWord.supportNodes r := by
    simp [VectorSkew.levelNodes, hz, hrz]
  have hwLevel :
      w.1 ∈ VectorSkew.levelNodes
        (f.vector.components j).toVariableWord.supportNodes r := by
    simp [VectorSkew.levelNodes, hw, hrw]
  have hzRow := (List.all_eq_true.mp hrow) z.1 hzLevel
  have hzw := (List.all_eq_true.mp hzRow) w.1 hwLevel
  simpa using hzw

/-- The vector family strictly separates adjacent intrinsic levels
across all coordinates, not merely within the same coordinate. -/
theorem local_lengths_lt_of_successive_level
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i j : Index c)
    (r : Nat) (hr : r < q - 1)
    (z w : BoundedNode b (k - (m + 1)))
    (hz : z.1 ∈ (f.vector.components i).toVariableWord.supportNodes)
    (hw : w.1 ∈ (f.vector.components j).toVariableWord.supportNodes)
    (hrz : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 = r)
    (hrw : SkewTree.heightAt
      (f.vector.components j).toVariableWord.supportNodes w.1 = r + 1) :
    z.1.length < w.1.length := by
  have hparts := f.vector.vector_complete
  simp only [VectorSkew.vectorCompleteB, Bool.and_eq_true] at hparts
  have hsucc : VectorSkew.successiveLevelsSeparatedB
      (fun i => (f.vector.components i).toVariableWord.supportNodes)
      q = true := by
    tauto
  unfold VectorSkew.successiveLevelsSeparatedB at hsucc
  have hrow :=
    (List.all_eq_true.mp hsucc) r (List.mem_range.mpr hr)
  have hi := (List.all_eq_true.mp hrow) i
    (DirectionalSupport.mem_allFin _ i)
  have hj := (List.all_eq_true.mp hi) j
    (DirectionalSupport.mem_allFin _ j)
  have hzLevel :
      z.1 ∈ VectorSkew.levelNodes
        (f.vector.components i).toVariableWord.supportNodes r := by
    simp [VectorSkew.levelNodes, hz, hrz]
  have hwLevel :
      w.1 ∈ VectorSkew.levelNodes
        (f.vector.components j).toVariableWord.supportNodes (r + 1) := by
    simp [VectorSkew.levelNodes, hw, hrw]
  have hzRow := (List.all_eq_true.mp hj) z.1 hzLevel
  have hzw := (List.all_eq_true.mp hzRow) w.1 hwLevel
  simpa using hzw

/-- The SAME-LEVEL clause of the mixed Ramsey word supplies
the precise hypothesis for the checked cross-frontier
projection order; this is a theorem about the ACTUAL P_i(z). -/
theorem projected_forward_order_equal_level
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i j : Index c)
    (hij : i < j)
    (r : Nat) (hr : r < q)
    (z w : BoundedNode b (k - (m + 1)))
    (hz : z.1 ∈ (f.vector.components i).toVariableWord.supportNodes)
    (hw : w.1 ∈ (f.vector.components j).toVariableWord.supportNodes)
    (hrz : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 = r)
    (hrw : SkewTree.heightAt
      (f.vector.components j).toVariableWord.supportNodes w.1 = r) :
    ForwardAux (projected c ⟨i,z⟩).1
      (projected c ⟨j,w⟩).1 := by
  exact projected_forward_order_of_tail_length_le
    c ⟨i,z⟩ ⟨j,w⟩ hij
    (local_lengths_le_of_equal_level c f i j hij
      r hr z w hz hw hrz hrw)

/-- Consecutive vector levels likewise give forward-ordered
projections whenever the frontier indices increase. -/
theorem projected_forward_order_successive_level
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i j : Index c)
    (hij : i < j)
    (r : Nat) (hr : r < q - 1)
    (z w : BoundedNode b (k - (m + 1)))
    (hz : z.1 ∈ (f.vector.components i).toVariableWord.supportNodes)
    (hw : w.1 ∈ (f.vector.components j).toVariableWord.supportNodes)
    (hrz : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 = r)
    (hrw : SkewTree.heightAt
      (f.vector.components j).toVariableWord.supportNodes w.1 = r + 1) :
    ForwardAux (projected c ⟨i,z⟩).1
      (projected c ⟨j,w⟩).1 := by
  apply projected_forward_order_of_tail_length_le
    c ⟨i,z⟩ ⟨j,w⟩ hij
  exact Nat.le_of_lt
    (local_lengths_lt_of_successive_level c f i j
      r hr z w hz hw hrz hrw)

/-- In particular, the candidate final support's projected
same-level roots satisfy the required ambient length inequality
across different sorted frontier indices. -/
theorem projected_length_le_equal_level
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i j : Index c)
    (hij : i < j)
    (r : Nat) (hr : r < q)
    (z w : BoundedNode b (k - (m + 1)))
    (hz : z.1 ∈ (f.vector.components i).toVariableWord.supportNodes)
    (hw : w.1 ∈ (f.vector.components j).toVariableWord.supportNodes)
    (hrz : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 = r)
    (hrw : SkewTree.heightAt
      (f.vector.components j).toVariableWord.supportNodes w.1 = r) :
    (projected c ⟨i,z⟩).1.length ≤
      (projected c ⟨j,w⟩).1.length := by
  exact projected_length_le_of_tail_length_le
    c ⟨i,z⟩ ⟨j,w⟩ hij
    (local_lengths_le_of_equal_level c f i j hij
      r hr z w hz hw hrz hrw)

/-- Successive local levels yield at least nondecreasing
projected ambient lengths, with strict local separation.
The strict projected inequality still requires controlling
frontier rank growth and will be proved independently. -/
theorem projected_length_le_successive_level
    {b n l k m q : Nat} {α β : Type*}
    (c : Frame b n l k m α)
    (f : LocalMixedWord c q β)
    (i j : Index c)
    (hij : i < j)
    (r : Nat) (hr : r < q - 1)
    (z w : BoundedNode b (k - (m + 1)))
    (hz : z.1 ∈ (f.vector.components i).toVariableWord.supportNodes)
    (hw : w.1 ∈ (f.vector.components j).toVariableWord.supportNodes)
    (hrz : SkewTree.heightAt
      (f.vector.components i).toVariableWord.supportNodes z.1 = r)
    (hrw : SkewTree.heightAt
      (f.vector.components j).toVariableWord.supportNodes w.1 = r + 1) :
    (projected c ⟨i,z⟩).1.length ≤
      (projected c ⟨j,w⟩).1.length := by
  apply projected_length_le_of_tail_length_le
    c ⟨i,z⟩ ⟨j,w⟩ hij
  exact Nat.le_of_lt
    (local_lengths_lt_of_successive_level c f i j
      r hr z w hz hw hrz hrw)

end DualTree.ForwardQFinalVectorOrdering
