import DualTree.ForwardCompleteBijection
import DualTree.CutPreservation

/-!
# Canonical addresses survive retention of an initial support cut

Let U be a forward-complete subset of a forward-complete support T.
If U retains every T vertex at or before a fixed ambient forward cut,
then the canonical address of each such vertex is unchanged. The two
complete supports may have different heights.

The geometric reason is local. An immediate T edge whose endpoints are
retained is still immediate in U. Completeness of U supplies its unique
directional successor, so every T traversal ending before the cut is
the same admissible traversal in U. Its new height bound follows from
the intrinsic rank of that traversal; it is not an extra assumption.

The final theorem applies this result to an actual uniform syntactic
refinement of complete variable words. Together with CutPreservation,
this gives stable addresses and rooted symbols in the retained initial
region, including for unary alphabets. It does not assert stability of
signature boundary markers outside that region, or enumerate the
model signature tasks needed for Lemma 28.
-/

namespace DualTree.ForwardCompleteInitialTransport

open ForwardCompleteEmbedding ForwardCompleteBijection

private theorem immediate_of_subset
    {b : Nat} (T U : List (Node b))
    (hsub : ∀ t, t ∈ U → t ∈ T)
    (s t : Node b) (ht : t ∈ U)
    (hstep : SkewTree.immediateSuccB T s t = true) :
    SkewTree.immediateSuccB U s t = true := by
  obtain ⟨_, hstrict, hno⟩ :=
    (SkewBranchGeometry.immediateSuccB_iff T s t).1 hstep
  apply (SkewBranchGeometry.immediateSuccB_iff U s t).2
  exact ⟨ht, hstrict, fun u hu => hno u (hsub u hu)⟩

private theorem walk_eq_of_retained_cut
    {b q : Nat} (T U : List (Node b))
    (hU : SkewTree.completeB SkewTree.forwardAuxB q U = true)
    (hnonU : U.length ≠ 1)
    (hsub : ∀ t, t ∈ U → t ∈ T)
    (cut : Node b)
    (hkeep : ∀ t, t ∈ T → ForwardAux t cut → t ∈ U) :
    ∀ (a s : Node b), s ∈ T →
      CanonicalSupportWalk.Admissible T s a →
      ForwardAux (CanonicalSupportWalk.walk T s a) cut →
      CanonicalSupportWalk.walk U s a =
        CanonicalSupportWalk.walk T s a ∧
      CanonicalSupportWalk.Admissible U s a := by
  intro a
  induction a with
  | nil =>
      intro s _ _ _
      exact ⟨rfl, trivial⟩
  | cons i tail ih =>
      intro s hs hvalid hbefore
      have hsBefore : ForwardAux s cut :=
        CutPreservation.forwardAux_of_prefix
          (CanonicalSupportWalk.walk_root_prefix T s (i :: tail)) hbefore
      have hsU : s ∈ U := hkeep s hs hsBefore
      have htT : CanonicalSupportWalk.next T s i ∈ T :=
        CanonicalSupportWalk.next_mem T s i hvalid.1
      have htBefore : ForwardAux (CanonicalSupportWalk.next T s i) cut :=
        CutPreservation.forwardAux_of_prefix
          (CanonicalSupportWalk.walk_root_prefix T
            (CanonicalSupportWalk.next T s i) tail) hbefore
      have htU : CanonicalSupportWalk.next T s i ∈ U :=
        hkeep _ htT htBefore
      have hstepT := CanonicalSupportWalk.next_unique T s i hvalid.1
      have hstepU : SkewTree.immediateSuccB U s
          (CanonicalSupportWalk.next T s i) = true :=
        immediate_of_subset T U hsub s _ htU hstepT.1
      have hbranchU : SkewTree.uniqueBranchB U s i = true :=
        unique_direction_of_immediate U hU hnonU s _ hsU hstepU i
      have hnext : CanonicalSupportWalk.next U s i =
          CanonicalSupportWalk.next T s i :=
        SupportReachability.next_eq_of_immediate U s _ i
          hbranchU hstepU hstepT.2
      obtain ⟨hwalk, htail⟩ := ih _ htT hvalid.2 hbefore
      constructor
      · change CanonicalSupportWalk.walk U
            (CanonicalSupportWalk.next U s i) tail = _
        rw [hnext]
        exact hwalk
      · change SkewTree.uniqueBranchB U s i = true ∧
          CanonicalSupportWalk.Admissible U
            (CanonicalSupportWalk.next U s i) tail
        exact ⟨hbranchU, by simpa only [hnext] using htail⟩

private theorem roots_eq_of_retained_cut
    {b k q : Nat} (T U : List (Node b))
    (hT : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hU : SkewTree.completeB SkewTree.forwardAuxB q U = true)
    (hnonT : T.length ≠ 1) (hnonU : U.length ≠ 1)
    (hsub : ∀ t, t ∈ U → t ∈ T)
    (cut : Node b)
    (hkeep : ∀ t, t ∈ T → ForwardAux t cut → t ∈ U)
    (t : Node b) (ht : t ∈ T) (hbefore : ForwardAux t cut) :
    rootOf U hU hnonU = rootOf T hT hnonT := by
  have hrootBefore : ForwardAux (rootOf T hT hnonT) cut :=
    CutPreservation.forwardAux_of_prefix
      (rootOf_prefix T hT hnonT t ht) hbefore
  have hrootU : rootOf T hT hnonT ∈ U :=
    hkeep _ (rootOf_mem T hT hnonT) hrootBefore
  exact isPrefix_antisymm
    (rootOf_prefix U hU hnonU _ hrootU)
    (rootOf_prefix T hT hnonT _
      (hsub _ (rootOf_mem U hU hnonU)))

/-- Every original model address ending in the retained initial region
is also bounded by the new complete height and has exactly the same
canonical image. No comparison between the two heights is assumed. -/
theorem canonicalEmbedding_transport
    {b k q : Nat} (T U : List (Node b))
    (hT : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hU : SkewTree.completeB SkewTree.forwardAuxB q U = true)
    (hnonT : T.length ≠ 1) (hnonU : U.length ≠ 1)
    (hsub : ∀ t, t ∈ U → t ∈ T)
    (cut : Node b)
    (hkeep : ∀ t, t ∈ T → ForwardAux t cut → t ∈ U)
    (a : BoundedNode b k)
    (hbefore : ForwardAux (canonicalEmbedding T hT hnonT a).1 cut) :
    ∃ a' : BoundedNode b q,
      a'.1 = a.1 ∧
      (canonicalEmbedding U hU hnonU a').1 =
        (canonicalEmbedding T hT hnonT a).1 := by
  have hroot := roots_eq_of_retained_cut T U hT hU hnonT hnonU
    hsub cut hkeep _ (canonicalEmbedding T hT hnonT a).2 hbefore
  have hvalidT : CanonicalSupportWalk.Admissible T
      (rootOf T hT hnonT) a.1 :=
    (canonical_bounded_address T hT hnonT a.1 a.2).1
  obtain ⟨hwalk, hvalidU⟩ :=
    walk_eq_of_retained_cut T U hU hnonU hsub cut hkeep
      a.1 (rootOf T hT hnonT) (rootOf_mem T hT hnonT) hvalidT hbefore
  have hvalid : CanonicalSupportWalk.Admissible U
      (rootOf U hU hnonU) a.1 := by
    simpa only [hroot] using hvalidU
  have hwalkMem : CanonicalSupportWalk.walk U
      (rootOf U hU hnonU) a.1 ∈ U :=
    CanonicalSupportWalk.walk_mem_of_admissible U _ a.1
      (rootOf_mem U hU hnonU) hvalid
  have hheight := SupportReachability.walk_height_of_admissible
    U (support_nodup U hU) a.1 (rootOf U hU hnonU)
      (rootOf_mem U hU hnonU) hvalid
  have hzero : SkewTree.heightAt U (rootOf U hU hnonU) = 0 :=
    ImmediateSupportHeight.heightAt_root_zero U _
      (rootOf_prefix U hU hnonU)
  have hlt := support_height_lt_k U hU _ hwalkMem
  have hbound : InHomTree q a.1 := by
    change a.1.length < q
    omega
  refine ⟨⟨a.1, hbound⟩, rfl, ?_⟩
  change CanonicalSupportWalk.walk U (rootOf U hU hnonU) a.1 =
    CanonicalSupportWalk.walk T (rootOf T hT hnonT) a.1
  simpa only [hroot] using hwalk

/-- An early retained vertex keeps its literal canonical address even
when the complete height changes. The equality compares finite nodes,
so it does not identify the different bounded-address subtypes. -/
theorem inverseAddress_eq_of_retained_cut
    {b k q : Nat} (T U : List (Node b))
    (hT : SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hU : SkewTree.completeB SkewTree.forwardAuxB q U = true)
    (hnonT : T.length ≠ 1) (hnonU : U.length ≠ 1)
    (hsub : ∀ t, t ∈ U → t ∈ T)
    (cut : Node b)
    (hkeep : ∀ t, t ∈ T → ForwardAux t cut → t ∈ U)
    (t : Node b) (ht : t ∈ T) (hbefore : ForwardAux t cut) :
    (inverseAddress U hU hnonU ⟨t, hkeep t ht hbefore⟩).1 =
      (inverseAddress T hT hnonT ⟨t, ht⟩).1 := by
  let a := inverseAddress T hT hnonT ⟨t, ht⟩
  have himage : (canonicalEmbedding T hT hnonT a).1 = t :=
    congrArg Subtype.val (inverse_right T hT hnonT ⟨t, ht⟩)
  have haBefore : ForwardAux (canonicalEmbedding T hT hnonT a).1 cut := by
    simpa only [himage] using hbefore
  obtain ⟨a', haddr, himage'⟩ :=
    canonicalEmbedding_transport T U hT hU hnonT hnonU
      hsub cut hkeep a haBefore
  have hvertex : canonicalEmbedding U hU hnonU a' =
      ⟨t, hkeep t ht hbefore⟩ :=
    Subtype.ext (himage'.trans himage)
  have hinverse : inverseAddress U hU hnonU
      ⟨t, hkeep t ht hbefore⟩ = a' := by
    rw [← hvertex, inverse_left]
  exact (congrArg Subtype.val hinverse).trans haddr

/-- The canonical complete-support address of an actual variable root. -/
noncomputable def variableAddress
    {b n k : Nat} {α : Type*}
    (f : KVariableWord b n k α SkewTree.forwardAuxB)
    (hnon : f.toVariableWord.supportNodes.length ≠ 1)
    (u : f.Vars) : BoundedNode b k :=
  inverseAddress f.toVariableWord.supportNodes f.complete_support hnon
    ⟨u.1.1, List.mem_map.mpr ⟨u.1, u.2, rfl⟩⟩

/-- Actual uniform syntactic refinement and initial-root retention
preserve the canonical model coordinate of every early variable.
No two-letter alphabet assumption or prescribed final height is used. -/
theorem variableAddress_eq_of_syntacticRefines
    {b n k q : Nat} {α : Type*}
    (f : KVariableWord b n k α SkewTree.forwardAuxB)
    (g : KVariableWord b n q α SkewTree.forwardAuxB)
    (hnonF : f.toVariableWord.supportNodes.length ≠ 1)
    (hnonG : g.toVariableWord.supportNodes.length ≠ 1)
    (hgf : KVariableWord.SyntacticRefines g f)
    (cut : Node b)
    (hkeep : ∀ u : f.Vars, ForwardAux u.1.1 cut → u.1 ∈ g.support)
    (u : f.Vars) (hbefore : ForwardAux u.1.1 cut) :
    (variableAddress g hnonG ⟨u.1, hkeep u hbefore⟩).1 =
      (variableAddress f hnonF u).1 := by
  have hsub : ∀ t, t ∈ g.toVariableWord.supportNodes →
      t ∈ f.toVariableWord.supportNodes := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact List.mem_map.mpr ⟨s,
      KVariableWord.support_subset_of_syntacticRefines g f hgf s hs, rfl⟩
  have hkeepNodes : ∀ t, t ∈ f.toVariableWord.supportNodes →
      ForwardAux t cut → t ∈ g.toVariableWord.supportNodes := by
    intro t ht htBefore
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact List.mem_map.mpr ⟨s, hkeep ⟨s, hs⟩ htBefore, rfl⟩
  exact inverseAddress_eq_of_retained_cut
    f.toVariableWord.supportNodes g.toVariableWord.supportNodes
    f.complete_support g.complete_support hnonF hnonG hsub cut hkeepNodes
    u.1.1 (List.mem_map.mpr ⟨u.1, u.2, rfl⟩) hbefore

end DualTree.ForwardCompleteInitialTransport
