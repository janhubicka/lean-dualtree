import DualTree.ForwardSemiCompleteAddressOrder
import DualTree.ForwardAuxFiniteMaximum
import DualTree.ForwardSourceBoundaryLeaves

/-!
# The canonical interior of every forward semi-complete starred tree

The first-l model in the corrected Definition 24 must describe every
eligible starred tree, without a supplied Q frame or complete extension.
For positive l we choose a maximal interior vertex, use the skew axiom
to identify the interior as an initial segment, and transport that segment
through the intrinsic directional-address equivalence. Strong induction
on the heap index rules out missing addresses; cardinality identifies
the segment with precisely the first l addresses.

The resulting equivalence also covers l=0. The maximal cut is only a
proof device and is absent from the final statement and canonical map.
-/

namespace DualTree.ForwardSemiCompleteInitial

open ForwardModelBoundaryHeap
open ForwardSemiCompleteZeroRoot
open ForwardSemiCompleteAddresses
open ForwardSemiCompleteAddressOrder

variable {b n l : Nat} {α : Type*}

/-- A maximal interior vertex; no ambient complete tree is part of this data. -/
structure InteriorCut
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) where
  point : Node b
  mem : point ∈ SkewTree.interior U.tree
  max : ∀ t, t ∈ SkewTree.interior U.tree → ForwardAux t point

/-- Positive interior cardinality supplies the finite maximal cut. -/
theorem interiorCut_nonempty
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (hl : 0 < l) :
    Nonempty (InteriorCut U) := by
  have hne : SkewTree.interior U.tree ≠ [] := by
    intro h
    have hc := U.interior_card
    rw [h] at hc
    simp only [List.length_nil] at hc
    omega
  obtain ⟨t, ht, hmax⟩ :=
    ForwardAuxFiniteMaximum.exists_maximal (SkewTree.interior U.tree) hne
  exact ⟨⟨t, ht, hmax⟩⟩

/-- The skew full-before clause makes every vertex before the cut interior. -/
theorem forward_le_cut_interior
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (c : InteriorCut U)
    (s : Node b) (hs : s ∈ U.tree) (hle : ForwardAux s c.point) :
    s ∈ SkewTree.interior U.tree := by
  by_cases heq : s = c.point
  · simpa [heq] using c.mem
  have hfull := StarredSignature.fullBefore_at_maxInterior
    U c.point c.mem (fun t ht => by
      simpa [SkewTree.forwardAuxB] using c.max t ht)
  unfold SkewTree.fullBeforeB at hfull
  have hbefore : SkewTree.forwardAuxB s c.point = true := by
    simpa [SkewTree.forwardAuxB] using hle
  have hentry : (SkewTree.allFin b).all
      (fun i => SkewTree.uniqueBranchB U.tree s i) = true := by
    have h := (List.all_eq_true.mp hfull) s hs
    simpa [hbefore, heq] using h
  let i : Fin b := ⟨0, hb⟩
  have hbranch : SkewTree.uniqueBranchB U.tree s i = true :=
    (List.all_eq_true.mp hentry) i (DirectionalSupport.mem_allFin b i)
  have hnext := CanonicalSupportWalk.next_unique U.tree s i hbranch
  have hnextMem := CanonicalSupportWalk.next_mem U.tree s i hbranch
  exact SignatureInteriorPersistence.interior_of_strict_descendant
    U.tree s (CanonicalSupportWalk.next U.tree s i) hs hnextMem
    ((SkewBranchGeometry.immediateSuccB_iff U.tree s
      (CanonicalSupportWalk.next U.tree s i)).1 hnext.1).2.1

/-- Exact interior initial-segment characterization on the support. -/
theorem interior_iff_forward_le_cut
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (c : InteriorCut U)
    (s : Node b) (hs : s ∈ U.tree) :
    s ∈ SkewTree.interior U.tree ↔ ForwardAux s c.point :=
  ⟨c.max s, forward_le_cut_interior hb U c s hs⟩

/-- The intrinsic address of the chosen cut. -/
noncomputable def cutAddress
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (c : InteriorCut U) : Address U :=
  (addressEquiv U).symm ⟨c.point, (List.mem_filter.mp c.mem).1⟩

theorem realize_cutAddress
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (c : InteriorCut U) :
    (realize U (cutAddress U c)).1 = c.point := by
  have h := (addressEquiv U).apply_symm_apply
    (⟨c.point, (List.mem_filter.mp c.mem).1⟩ : Vertex U)
  exact congrArg Subtype.val h

/-- Interior addresses are initially characterized among admissible addresses. -/
theorem address_interior_iff_heap_le_cut
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (c : InteriorCut U)
    (u : Address U) :
    (realize U u).1 ∈ SkewTree.interior U.tree ↔
      heapIndex u.1 ≤ heapIndex (cutAddress U c).1 := by
  have horder := forwardAux_realize_iff U u (cutAddress U c)
  rw [realize_cutAddress U c] at horder
  exact (interior_iff_forward_le_cut hb U c (realize U u).1
    (realize U u).2).trans
    (horder.symm.trans
      (ForwardModelHeapInjective.forwardAux_iff_heapIndex_le
        hb u.1 (cutAddress U c).1))

/-- No homogeneous address before the final interior address is missing. -/
theorem heap_le_cut_admissible
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (c : InteriorCut U)
    (a : Node b) (hle : heapIndex a ≤ heapIndex (cutAddress U c).1) :
    CanonicalSupportWalk.Admissible U.tree (starredRootAll U) a := by
  let N := heapIndex (cutAddress U c).1
  have hmain : ∀ q : Nat, q ≤ N → ∀ a : Node b, heapIndex a = q →
      CanonicalSupportWalk.Admissible U.tree (starredRootAll U) a := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
        intro hq a ha
        cases hrev : a.reverse with
        | nil =>
            have haNil : a = [] := by
              have h := congrArg List.reverse hrev
              simpa using h
            simp [haNil, CanonicalSupportWalk.Admissible]
        | cons i revParent =>
            let p : Node b := revParent.reverse
            have hrepr : a = p ++ [i] := by
              have h := congrArg List.reverse hrev
              simpa [p] using h
            have hpSmaller : heapIndex p < q := by
              have hlt := heapIndex_lt_child hb p i
              rw [hrepr] at ha
              omega
            have hple : heapIndex p ≤ N := by omega
            have hpValid := ih (heapIndex p) hpSmaller hple p rfl
            let parent : Address U := ⟨p, hpValid⟩
            have hpInterior : (realize U parent).1 ∈
                SkewTree.interior U.tree :=
              (address_interior_iff_heap_le_cut hb U c parent).2 hple
            have hbranch : SkewTree.uniqueBranchB U.tree
                (CanonicalSupportWalk.walk U.tree (starredRootAll U) p) i = true :=
              full_directions U (realize U parent).1 hpInterior i
            rw [hrepr]
            exact (ForwardSourceBoundaryLeaves.admissible_append_singleton_iff
              U.tree (starredRootAll U) p i).2 ⟨hpValid, hbranch⟩
  exact hmain (heapIndex a) hle a rfl

/-- Every address in this interval realizes an interior vertex. -/
theorem heap_le_cut_iff_interior_address
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (c : InteriorCut U) (a : Node b) :
    heapIndex a ≤ heapIndex (cutAddress U c).1 ↔
      ∃ u : Address U, u.1 = a ∧
        (realize U u).1 ∈ SkewTree.interior U.tree := by
  constructor
  · intro hle
    let u : Address U := ⟨a, heap_le_cut_admissible hb U c a hle⟩
    exact ⟨u, rfl, (address_interior_iff_heap_le_cut hb U c u).2 hle⟩
  · rintro ⟨u, hu, hint⟩
    rw [← hu]
    exact (address_interior_iff_heap_le_cut hb U c u).1 hint

/-- Counting the entire interval determines its endpoint exactly. -/
theorem cut_heapIndex_succ_eq_l
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (c : InteriorCut U) :
    heapIndex (cutAddress U c).1 + 1 = l := by
  classical
  let N := heapIndex (cutAddress U c).1 + 1
  let f : {a : Node b // ModelInterior N a} →
      {t : Node b // t ∈ SkewTree.interior U.tree} := fun a =>
    let u : Address U := ⟨a.1, heap_le_cut_admissible hb U c a.1
      (Nat.lt_succ_iff.mp a.2)⟩
    ⟨(realize U u).1,
      (address_interior_iff_heap_le_cut hb U c u).2
        (Nat.lt_succ_iff.mp a.2)⟩
  have hinj : Function.Injective f := by
    intro a d had
    apply Subtype.ext
    exact CanonicalSupportInjective.walk_injective_of_admissible
      U.tree a.1 (starredRootAll U) d.1
      (heap_le_cut_admissible hb U c a.1 (Nat.lt_succ_iff.mp a.2))
      (heap_le_cut_admissible hb U c d.1 (Nat.lt_succ_iff.mp d.2))
      (congrArg Subtype.val had)
  have hsurj : Function.Surjective f := by
    intro t
    obtain ⟨a, hadm, hwalk, _⟩ :=
      has_address U t.1 (List.mem_filter.mp t.2).1
    let u : Address U := ⟨a, hadm⟩
    have hint : (realize U u).1 ∈ SkewTree.interior U.tree := by
      change canonicalWalkAll U a ∈ _
      rw [hwalk]
      exact t.2
    have hle := (address_interior_iff_heap_le_cut hb U c u).1 hint
    refine ⟨⟨a, Nat.lt_succ_of_le hle⟩, ?_⟩
    apply Subtype.ext
    exact hwalk
  have hnd : (SkewTree.interior U.tree).Nodup :=
    (support_nodup U).filter _
  have hcard : Nat.card {t : Node b // t ∈ SkewTree.interior U.tree} =
      (SkewTree.interior U.tree).length := by
    change Nat.card ({t : Node b | t ∈ SkewTree.interior U.tree} :
      Set (Node b)) = _
    rw [Nat.card_coe_set_eq, List.ncard_ofPred_mem, hnd.dedup]
  calc
    heapIndex (cutAddress U c).1 + 1 =
        Nat.card {a : Node b // ModelInterior N a} :=
      (ForwardModelHeapSurjective.modelInterior_card hb N).symm
    _ = Nat.card {t : Node b // t ∈ SkewTree.interior U.tree} :=
      Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
    _ = (SkewTree.interior U.tree).length := hcard
    _ = l := U.interior_card

/-- On every eligible U, including l=0, the first l model addresses
are exactly the admissible addresses of its interior vertices. -/
theorem modelInterior_iff_interior_address
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Node b) :
    ModelInterior l a ↔
      ∃ u : Address U, u.1 = a ∧
        (realize U u).1 ∈ SkewTree.interior U.tree := by
  by_cases hl : l = 0
  · have hnil : SkewTree.interior U.tree = [] :=
      List.length_eq_zero_iff.mp (U.interior_card.trans hl)
    simp [ModelInterior, hl, hnil]
  · obtain ⟨c⟩ := interiorCut_nonempty U (Nat.pos_of_ne_zero hl)
    have hcount := cut_heapIndex_succ_eq_l hb U c
    have hcmp : ModelInterior l a ↔
        heapIndex a ≤ heapIndex (cutAddress U c).1 := by
      unfold ModelInterior
      omega
    exact hcmp.trans (heap_le_cut_iff_interior_address hb U c a)

/-- The canonical walk is valid on the entire first-l interior. -/
theorem modelInterior_admissible
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Node b)
    (ha : ModelInterior l a) :
    CanonicalSupportWalk.Admissible U.tree (starredRootAll U) a := by
  obtain ⟨u, hu, _⟩ := (modelInterior_iff_interior_address hb U a).1 ha
  rw [← hu]
  exact u.2

/-- The intrinsic selector sends every model interior node to an actual interior. -/
theorem canonicalWalkAll_interior
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Node b)
    (ha : ModelInterior l a) :
    canonicalWalkAll U a ∈ SkewTree.interior U.tree := by
  obtain ⟨u, hu, hint⟩ := (modelInterior_iff_interior_address hb U a).1 ha
  change CanonicalSupportWalk.walk U.tree (starredRootAll U) a ∈ _
  rw [← hu]
  exact hint

end DualTree.ForwardSemiCompleteInitial
