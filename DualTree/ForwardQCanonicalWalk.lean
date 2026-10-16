import DualTree.ForwardQModelSuccessor
import DualTree.ForwardCanonicalPartialWalkUniqueness
import DualTree.ForwardQModelBoundaryTransport

/-!
# Actual corrected Q is the canonical directional support walk

The verified model-to-Q equivalence preserves the full model prefix
order and labelled child cones. ForwardQModelSuccessor now proves that
each concrete model child is precisely the immediate directional
successor in the FINITE Q SUPPORT, not necessarily an immediate
ambient homogeneous-tree child.

This module turns the local result into a finite-model canonical
walk theorem. We totalize the model vertex realization on arbitrary
homogeneous addresses merely to invoke the earlier rigidity lemma;
its off-model fallback carries no mathematical information.

The root is proved to be the actual original source root, using
the independently verified equality of source interior cardinality
and first-l heap size. On the genuine model A_l boundary the walk
thus selects exactly the marked D2 projection, and on the actual
finished fibrewise Q starred outputs agrees with the verified
source-relative A_l selector.

This does NOT yet identify the canonical selector on arbitrary
semi-complete starred U with the printed Definition 24, reconcile
the printed reverse order with the forward model, or establish the
mixed span/Hall or Ramsey recursion.
-/

namespace DualTree.ForwardQCanonicalWalk

open ForwardSourceQTree
open ForwardModelBoundaryHeap
open ForwardQModelVertexEquiv
open ForwardQModelPrefixIso
open ForwardQModelSuccessor
open ForwardQModelBoundaryTransport
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord

/-- A total address map agreeing with the genuine model/Q realization
on H_l ⊕ A_l. Its value away from the model is an arbitrary fallback:
only its restriction to H_l ∪ A_l will be used. -/
noncomputable def modelQAddressImage
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) (a : Node b) : Node b := by
  classical
  exact if h : ModelInterior l a then
    ((modelQVertexEquiv hb c x) (Sum.inl ⟨a, h⟩)).1
  else if h : ModelBoundary l a then
    ((modelQVertexEquiv hb c x) (Sum.inr ⟨a, h⟩)).1
  else
    ForwardQRooted.sourceRoot c

/-- On every legitimate model address, the total map is
the actual corrected Q vertex, with no arbitrary-choice loss. -/
theorem modelQAddressImage_atShape
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (v : ModelShape c) :
    modelQAddressImage hb c x (modelAddress v) =
      ((modelQVertexEquiv hb c x) v).1 := by
  classical
  cases v with
  | inl p =>
      simp [modelQAddressImage, modelAddress, p.2]
  | inr a =>
      simp [modelQAddressImage, modelAddress, a.2.1, a.2]

/-- The canonical model/Q realization of the empty address is
the ACTUAL retained original source root. The first-l interior
is nonempty because it has exactly the source's interior size. -/
theorem modelQAddressImage_root
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    modelQAddressImage hb c x ([] : Node b) =
      ForwardQRooted.sourceRoot c := by
  have hcount := ForwardSourceInteriorFirstL.cut_heapIndex_succ_eq_l hb c
  have hl : 0 < l := by omega
  have hroot : ModelInterior l ([] : Node b) := by
    simpa [ModelInterior, heapIndex] using hl
  let p : ModelInteriorVertex c := ⟨[], hroot⟩
  have hvalue := modelQAddressImage_atShape hb c x (Sum.inl p)
  change modelQAddressImage hb c x [] =
    ((modelQVertexEquiv hb c x) (Sum.inl p)).1 at hvalue
  calc
    modelQAddressImage hb c x [] =
        ((modelQVertexEquiv hb c x) (Sum.inl p)).1 := hvalue
    _ = ((modelInteriorSourceEquiv hb c) p).1 :=
      modelQ_interior_value hb c x p
    _ = CanonicalSupportWalk.walk c.source.tree
          (ForwardQRooted.sourceRoot c) p.1 :=
      ForwardSourceAddressPrefixIso.modelInteriorSourceEquiv_value hb c p
    _ = ForwardQRooted.sourceRoot c := rfl

/-- Every first-l model parent obeys the genuine Q-support
local successor recursion. The intervening ambient levels do
not enter: the successor is in the finite support. -/
theorem modelQAddressImage_step
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (p : Node b) (i : Fin b)
    (hp : ModelInterior l p) :
    modelQAddressImage hb c x (p ++ [i]) =
      CanonicalSupportWalk.next (nodes c x).toList
        (modelQAddressImage hb c x p) i := by
  let v : ModelInteriorVertex c := ⟨p, hp⟩
  have hparent := modelQAddressImage_atShape hb c x (Sum.inl v)
  change modelQAddressImage hb c x p =
    ((modelQVertexEquiv hb c x) (Sum.inl v)).1 at hparent
  have hchild := modelQAddressImage_atShape hb c x (modelChild c v i)
  rw [modelChild_address] at hchild
  calc
    modelQAddressImage hb c x (p ++ [i]) =
        ((modelQVertexEquiv hb c x) (modelChild c v i)).1 := hchild
    _ = CanonicalSupportWalk.next (nodes c x).toList
        ((modelQVertexEquiv hb c x) (Sum.inl v)).1 i :=
      (modelQ_next_eq_modelChild hb c x v i).symm
    _ = CanonicalSupportWalk.next (nodes c x).toList
        (modelQAddressImage hb c x p) i :=
      congrArg (fun s : Node b =>
        CanonicalSupportWalk.next (nodes c x).toList s i) hparent.symm

/-- The homogeneous model's canonical finite directional walk
is EXACTLY the genuine model/Q vertex realization, throughout
both sorts of H_l ⊕ A_l. -/
theorem modelQWalk_realizes_all
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (v : ModelShape c) :
    CanonicalSupportWalk.walk (nodes c x).toList
      (ForwardQRooted.sourceRoot c) (modelAddress v) =
      ((modelQVertexEquiv hb c x) v).1 := by
  have hv : ModelInterior l (modelAddress v) ∨
      ModelBoundary l (modelAddress v) := by
    cases v with
    | inl p => exact Or.inl p.2
    | inr a => exact Or.inr a.2
  have hrigid :=
    ForwardCanonicalPartialWalkUniqueness.unique_model_map_eq_support_walk
      hb (nodes c x).toList
      (modelQAddressImage hb c x [])
      (modelQAddressImage hb c x)
      rfl
      (fun p i hp => modelQAddressImage_step hb c x p i hp)
      (modelAddress v) hv
  calc
    CanonicalSupportWalk.walk (nodes c x).toList
        (ForwardQRooted.sourceRoot c) (modelAddress v) =
      CanonicalSupportWalk.walk (nodes c x).toList
        (modelQAddressImage hb c x []) (modelAddress v) := by
          rw [modelQAddressImage_root hb c x]
    _ = modelQAddressImage hb c x (modelAddress v) := hrigid.symm
    _ = ((modelQVertexEquiv hb c x) v).1 :=
      modelQAddressImage_atShape hb c x v

/-- Crucial Q-side Definition 24 boundary identity:
the walk at every genuine A_l address is precisely the
ACTUAL corrected Q projected D2 marked point. -/
theorem modelQWalk_boundary
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (a : ModelA c) :
    CanonicalSupportWalk.walk (nodes c x).toList
      (ForwardQRooted.sourceRoot c) a.1 =
      (markedProjection c x ((modelAToD2 hb c) a)).1 := by
  have h := modelQWalk_realizes_all hb c x (Sum.inr a)
  change CanonicalSupportWalk.walk (nodes c x).toList
    (ForwardQRooted.sourceRoot c) a.1 =
      ((modelQVertexEquiv hb c x) (Sum.inr a)).1 at h
  exact h.trans (modelQ_terminal_value hb c x a)

/-- On every ACTUAL finished starred Q output the canonical
Q-support walk at A_l agrees with the existing relative selector,
whose value was independently verified to be the real D2 point. -/
theorem modelQWalk_actual_starred_eq_relative_selector
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (a : ModelA c.core) :
    CanonicalSupportWalk.walk
      (fibreQStarredWord hb c fallback w).tree
      (ForwardQRooted.sourceRoot c.core) a.1 =
    canonicalModelATerminal hb c.core
      (fibreQStarredWord hb c fallback w) a := by
  rw [fibreQStarredWord_tree]
  exact
    (modelQWalk_boundary hb c.core
      (ForwardQEnlargedConstantWords.eraseAux c.core fallback w.1) a).trans
    (canonicalModelATerminal_actual_Q hb c fallback w a).symm

/-- A simple, explicitly SOURCE-ROOTED canonical walk on arbitrary
starred outputs. This is NOT silently assumed to equal the paper's
rooted I_U when U has a different root. -/
noncomputable def sourceRootedModelPoint
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a : ModelA c) : Node b :=
  CanonicalSupportWalk.walk U.tree
    (ForwardQRooted.sourceRoot c) a.1

/-- The SOURCE-ROOTED walk has genuine Q-local agreement
without an additional selector hypothesis. -/
theorem sourceRootedModelPoint_Qlocal
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (a : ModelA c.core) :
    sourceRootedModelPoint hb c.core
      (fibreQStarredWord hb c fallback w) a =
      canonicalModelATerminal hb c.core
        (fibreQStarredWord hb c fallback w) a :=
  modelQWalk_actual_starred_eq_relative_selector hb c fallback w a

end DualTree.ForwardQCanonicalWalk
