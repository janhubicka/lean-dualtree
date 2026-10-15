import DualTree.ForwardSourceHeapInitial
import DualTree.ForwardModelHeapSurjective

/-!
# The genuine source interior occupies exactly the first l heap addresses

The previous module proves that every homogeneous address with
heap index at most that of the last interior source cut is
admissible, and is an interior address. Conversely each source
interior address lies in that interval.

Here we turn this into an explicit equivalence between the full
heap interval and the source interior, then compare cardinalities
with the source's given number l of interior vertices.

Thus if N is the heap index of the canonical cut address, then
N + 1 = l. Consequently the complete source interior consists of
EXACTLY the first l addresses in corrected forward breadth-first
order: no addresses are skipped or duplicated.

This is the model INTERIOR identification. The canonical external
model boundary A_l to source leaves, and the resulting A_l to
literal R marker equivalence, remain separate.
-/

namespace DualTree.ForwardSourceInteriorFirstL

open ForwardSourceQTree
open ForwardSourceCanonicalAddresses
open ForwardSourceAddressOrder
open ForwardSourceHeapInitial
open ForwardModelBoundaryHeap

/-- The source interior subtype, using the original source support,
rather than nodes of the reconstructed corrected Q output. -/
abbrev SourceInterior
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  {s : Node b // s ∈ SkewTree.interior c.source.tree}

/-- The full arithmetic initial model, terminated at the heap
index of the canonical address of the last interior cut. -/
abbrev InitialCutModel
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  {a : Node b //
    ModelInterior (heapIndex (cutAddress c).1 + 1) a}

/-- Realize each full model initial address as the original
interior vertex reached by its canonical source support walk.
Full admissibility is the genuine source-facing theorem. -/
noncomputable def realizeInitialCut
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    InitialCutModel c → SourceInterior c := by
  intro a
  have hle : heapIndex a.1 ≤ heapIndex (cutAddress c).1 :=
    Nat.lt_succ_iff.mp a.2
  let u : SourceAddress c :=
    ⟨a.1, heap_le_cut_admissible hb c a.1 hle⟩
  refine ⟨(realize c u).1, ?_⟩
  exact (address_interior_iff_forward_le_cut hb c u).2
    ((ForwardModelHeapInjective.forwardAux_iff_heapIndex_le
      hb a.1 (cutAddress c).1).2 hle)

/-- The full heap interval cannot contain two addresses naming
one source interior vertex, by injectivity of directional walks. -/
theorem realizeInitialCut_injective
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    Function.Injective (realizeInitialCut hb c) := by
  intro a d had
  have hleA : heapIndex a.1 ≤ heapIndex (cutAddress c).1 :=
    Nat.lt_succ_iff.mp a.2
  have hleD : heapIndex d.1 ≤ heapIndex (cutAddress c).1 :=
    Nat.lt_succ_iff.mp d.2
  let u : SourceAddress c :=
    ⟨a.1, heap_le_cut_admissible hb c a.1 hleA⟩
  let v : SourceAddress c :=
    ⟨d.1, heap_le_cut_admissible hb c d.1 hleD⟩
  have hraw :
      (realizeInitialCut hb c a).1 =
        (realizeInitialCut hb c d).1 :=
    congrArg Subtype.val had
  change (realize c u).1 = (realize c v).1 at hraw
  have huv : u = v :=
    realize_injective c (Subtype.ext hraw)
  have haddr : a.1 = d.1 := by
    exact congrArg Subtype.val huv
  exact Subtype.ext haddr

/-- Every source interior vertex is in the realized heap
initial interval; this uses surjectivity of the source canonical
address map and the already verified cut-index bound. -/
theorem realizeInitialCut_surjective
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    Function.Surjective (realizeInitialCut hb c) := by
  intro t
  obtain ⟨a, hadm, hwalk, _⟩ :=
    source_has_address c t.1 (List.mem_filter.mp t.2).1
  let u : SourceAddress c := ⟨a, hadm⟩
  have hinterior : (realize c u).1 ∈
      SkewTree.interior c.source.tree := by
    change (CanonicalSupportWalk.walk c.source.tree
      (ForwardQRooted.sourceRoot c) a) ∈
        SkewTree.interior c.source.tree
    rw [hwalk]
    exact t.2
  have hle : heapIndex a ≤ heapIndex (cutAddress c).1 :=
    interior_address_heap_le_cut hb c u hinterior
  let model : InitialCutModel c := ⟨a, Nat.lt_succ_of_le hle⟩
  refine ⟨model, ?_⟩
  apply Subtype.ext
  change (CanonicalSupportWalk.walk c.source.tree
    (ForwardQRooted.sourceRoot c) a) = t.1
  exact hwalk

/-- The first N+1 homogeneous heap addresses correspond exactly,
and without arbitrary choices, to all original source interiors. -/
noncomputable def initialCutInteriorEquiv
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    InitialCutModel c ≃ SourceInterior c :=
  Equiv.ofBijective (realizeInitialCut hb c)
    ⟨realizeInitialCut_injective hb c,
      realizeInitialCut_surjective hb c⟩

/-- The last source interior cut has zero-based forward heap index
exactly l-1: the full source interior has l vertices, and the
whole initial heap interval has one vertex per integer index. -/
theorem cut_heapIndex_succ_eq_l
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) :
    heapIndex (cutAddress c).1 + 1 = l := by
  classical
  let L := SkewTree.interior c.source.tree
  have hparts := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hparts
  have hskew := hparts.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  have hsourceNodup : c.source.tree.Nodup := by
    simpa using hskew.1
  have hLnodup : L.Nodup := hsourceNodup.filter _
  have hcardL : Nat.card (SourceInterior c) = L.length := by
    change Nat.card ({t : Node b | t ∈ L} : Set (Node b)) =
      L.length
    rw [Nat.card_coe_set_eq, List.ncard_ofPred_mem, hLnodup.dedup]
  calc
    heapIndex (cutAddress c).1 + 1 =
        Nat.card (InitialCutModel c) := by
      exact (ForwardModelHeapSurjective.modelInterior_card
        hb (heapIndex (cutAddress c).1 + 1)).symm
    _ = Nat.card (SourceInterior c) :=
      Nat.card_congr (initialCutInteriorEquiv hb c)
    _ = L.length := hcardL
    _ = l := c.source.interior_card

/-- Definition 24's first l homogeneous model vertices are
EXACTLY the admissible addresses whose actual source
realizations lie in the original interior. -/
theorem modelInterior_iff_sourceInterior_address
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (a : Node b) :
    ModelInterior l a ↔
      ∃ u : SourceAddress c,
        u.1 = a ∧
        (realize c u).1 ∈ SkewTree.interior c.source.tree := by
  have hcount := cut_heapIndex_succ_eq_l hb c
  change heapIndex a < l ↔ _
  have hcmp :
      heapIndex a < l ↔ heapIndex a ≤
        heapIndex (cutAddress c).1 := by omega
  exact hcmp.trans
    (heap_le_cut_iff_source_interior_address hb c a)

end DualTree.ForwardSourceInteriorFirstL
