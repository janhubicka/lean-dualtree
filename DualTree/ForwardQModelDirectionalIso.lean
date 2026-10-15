import DualTree.ForwardSourceAddressChildCone
import DualTree.ForwardQModelPrefixIso
import DualTree.ForwardQModelLeafIncidence

/-!
# The genuine corrected Q realization preserves all model directions

The verified complete corrected-model prefix isomorphism was not
sufficient to rule out permutation of sibling directions.
A separate source-facing theorem now proves first-direction
preservation/reflection.

For each first-l model interior address p, every model interior
or external-boundary address v, and every outgoing i<b, the model
cone p++[i] contains v if and only if the ACTUAL corrected Q
node representing v lies in the ambient i-cone of the Q node
representing p.

The interior/interior case is the new direction-labelled
semi-complete source admissible-walk theorem. In the
interior/boundary case the same theorem compares the original
source interior and source leaf; the independently verified
source-leaf/literal-R/Q directional-incidence lemma then
transfers to the projected Q marked terminal.

This completes the model's OWN prefix and direction-labelled
finite support-tree geometry on genuine corrected Q outputs.
It still does NOT equate the source-relative terminal map with
the published Definition 24 I_U on every arbitrary starred
refinement U, or solve mixed word span and Ramsey recursion.
-/

namespace DualTree.ForwardQModelDirectionalIso

open ForwardSourceQTree
open ForwardSourceCanonicalAddresses
open ForwardSourceInteriorFirstL
open ForwardSourceBoundaryEquiv
open ForwardSourceAddressChildCone
open ForwardQModelVertexEquiv
open ForwardQModelBoundaryTransport
open ForwardModelBoundaryHeap

/-- At any genuine first-l model interior p, the precise outgoing
direction of every other first-l model vertex is preserved AND
reflected by the actual corrected Q realization, including its
genuinely moving projected external-boundary terminals. -/
theorem modelQ_childCone_iff_modelAddress
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (p : ModelInteriorVertex c)
    (v : ModelShape c)
    (i : Fin b) :
    IsPrefix (p.1 ++ [i])
      (ForwardQModelPrefixIso.modelAddress v) ↔
    IsPrefix
      (((modelQVertexEquiv hb c x) (Sum.inl p)).1 ++ [i])
      ((modelQVertexEquiv hb c x) v).1 := by
  have hcount := cut_heapIndex_succ_eq_l hb c
  have hpLe : heapIndex p.1 ≤
      heapIndex (ForwardSourceAddressOrder.cutAddress c).1 := by
    have hp : heapIndex p.1 < l := p.2
    omega
  let up : SourceAddress c :=
    ⟨p.1, ForwardSourceHeapInitial.heap_le_cut_admissible
      hb c p.1 hpLe⟩
  cases v with
  | inl d =>
      have hdLe : heapIndex d.1 ≤
          heapIndex (ForwardSourceAddressOrder.cutAddress c).1 := by
        have hd : heapIndex d.1 < l := d.2
        omega
      let ud : SourceAddress c :=
        ⟨d.1, ForwardSourceHeapInitial.heap_le_cut_admissible
          hb c d.1 hdLe⟩
      have hdir :=
        sourceAddress_childCone_iff c up ud i
      change IsPrefix (p.1 ++ [i]) d.1 ↔
        IsPrefix
          (((modelQVertexEquiv hb c x) (Sum.inl p)).1 ++ [i])
          ((modelQVertexEquiv hb c x) (Sum.inl d)).1
      rw [modelQ_interior_value hb c x p,
        modelQ_interior_value hb c x d]
      rw [ForwardSourceAddressPrefixIso.modelInteriorSourceEquiv_value
        hb c p,
        ForwardSourceAddressPrefixIso.modelInteriorSourceEquiv_value
        hb c d]
      exact hdir
  | inr a =>
      let ua : SourceAddress c :=
        ⟨a.1, ForwardSourceBoundaryLeaves.modelBoundary_admissible
          hb c a⟩
      have hdir :=
        sourceAddress_childCone_iff c up ua i
      have hsource :
          IsPrefix (p.1 ++ [i]) a.1 ↔
          IsPrefix
            (((modelInteriorSourceEquiv hb c) p).1 ++ [i])
            ((boundarySourceLeafEquiv hb c) a).1 := by
        rw [ForwardSourceAddressPrefixIso.modelInteriorSourceEquiv_value
          hb c p, ForwardQModelPrefixIso.boundarySourceLeafEquiv_value
          hb c a]
        change IsPrefix (up.1 ++ [i]) ua.1 ↔
          IsPrefix ((realize c up).1 ++ [i]) (realize c ua).1
        exact hdir
      have hproject :=
        ForwardQModelLeafIncidence.model_Q_childCone_iff_source_leaf
          hb c x a
          ((modelInteriorSourceEquiv hb c) p).1
          ((modelInteriorSourceEquiv hb c) p).2 i
      change IsPrefix (p.1 ++ [i]) a.1 ↔
        IsPrefix
          (((modelQVertexEquiv hb c x) (Sum.inl p)).1 ++ [i])
          ((modelQVertexEquiv hb c x) (Sum.inr a)).1
      rw [modelQ_interior_value hb c x p,
        modelQ_terminal_value hb c x a]
      exact hsource.trans hproject.symm

/-- All canonical model prefix AND first-direction comparisons
hold for the ACTUAL Q support at once. This is the precise
finite direction-labelled tree geometry of the corrected Q
model, not an assumption about published arbitrary-U selectors. -/
theorem modelQ_prefix_and_childCones
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    (∀ u v : ModelShape c,
      IsPrefix
        (ForwardQModelPrefixIso.modelAddress u)
        (ForwardQModelPrefixIso.modelAddress v) ↔
      IsPrefix
        ((modelQVertexEquiv hb c x) u).1
        ((modelQVertexEquiv hb c x) v).1) ∧
    (∀ (p : ModelInteriorVertex c) (v : ModelShape c)
      (i : Fin b),
      IsPrefix (p.1 ++ [i])
        (ForwardQModelPrefixIso.modelAddress v) ↔
      IsPrefix
        (((modelQVertexEquiv hb c x) (Sum.inl p)).1 ++ [i])
        ((modelQVertexEquiv hb c x) v).1) := by
  constructor
  · intro u v
    exact
      (ForwardQModelPrefixIso.modelQ_prefix_iff_modelAddress
        hb c x u v).symm
  · intro p v i
    exact modelQ_childCone_iff_modelAddress hb c x p v i

end DualTree.ForwardQModelDirectionalIso
