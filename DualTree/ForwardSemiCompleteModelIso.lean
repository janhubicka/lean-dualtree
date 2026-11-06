import DualTree.ForwardSemiCompleteBoundary

/-!
# The whole corrected Definition-24 model is canonically isomorphic to U

For every eligible semi-complete starred support U, the intrinsic walk
identifies the first-l model interior together with its external boundary
with the entire support of U. At l=0 the model is the singleton empty
address. The map preserves and reflects prefix, lexicographic, and
corrected forward auxiliary order, and it identifies the model interior
and boundary with the actual interior and leaves respectively.

This validates a precise semi-complete extension of the canonical map
used in Definition 24. The corrected auxiliary order is part of the
statement; the paper's incompatible printed reverse-lexicographic order
is not identified with it.
-/

namespace DualTree.ForwardSemiCompleteModelIso

open ForwardModelBoundaryHeap
open ForwardCanonicalPartialWalkUniqueness
open ForwardSemiCompleteZeroRoot
open ForwardSemiCompleteAddresses
open ForwardSemiCompleteAddressOrder
open ForwardSemiCompleteInitial
open ForwardSemiCompleteBoundary

variable {b n l : Nat} {α : Type*}

/-- The root choice depends only on the support tree, not on the word,
its dependent variable type, or the proof used to certify the support. -/
theorem starredRootAll_eq_of_tree_eq
    (U V : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (h : U.tree = V.tree) :
    starredRootAll U = starredRootAll V := by
  apply isPrefix_antisymm
  · apply starredRootAll_prefix U
    rw [h]
    exact starredRootAll_mem V
  · apply starredRootAll_prefix V
    rw [← h]
    exact starredRootAll_mem U

/-- The canonical selector I_S is independent of the accompanying word g. -/
theorem canonicalWalkAll_eq_of_tree_eq
    (U V : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (h : U.tree = V.tree) (a : Node b) :
    canonicalWalkAll U a = canonicalWalkAll V a := by
  unfold canonicalWalkAll
  rw [h, starredRootAll_eq_of_tree_eq U V h]

/-- The complete finite model, with its exceptional zero-interior boundary. -/
abbrev Model (b l : Nat) :=
  {a : Node b // ModelInterior l a ∨ Definition24Boundary l a}

/-- Every address of the whole model follows actual unique support branches. -/
theorem model_admissible
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Model b l) :
    CanonicalSupportWalk.Admissible U.tree (starredRootAll U) a.1 := by
  rcases a.2 with hint | hboundary
  · exact modelInterior_admissible hb U a.1 hint
  · exact boundary_admissible hb U ⟨a.1, hboundary⟩

/-- Every admissible address belongs to the stated model; the walk has no
additional valid branches beyond its interior and external boundary. -/
theorem address_in_model
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Address U) :
    ModelInterior l a.1 ∨ Definition24Boundary l a.1 := by
  by_cases hint : (realize U a).1 ∈ SkewTree.interior U.tree
  · exact Or.inl ((modelInterior_iff_interior_address hb U a.1).2
      ⟨a, rfl, hint⟩)
  · exact Or.inr (leaf_address_boundary hb U a hint)

/-- The first-l model is exactly the set of admissible addresses. -/
noncomputable def modelAddressEquiv
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Model b l ≃ Address U where
  toFun a := ⟨a.1, model_admissible hb U a⟩
  invFun a := ⟨a.1, address_in_model hb U a⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The corrected semi-complete canonical map from the entire model onto U. -/
noncomputable def modelVertexEquiv
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Model b l ≃ Vertex U :=
  (modelAddressEquiv hb U).trans (addressEquiv U)

/-- The canonical isomorphism is the already defined intrinsic walk. -/
@[simp] theorem modelVertexEquiv_value
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Model b l) :
    ((modelVertexEquiv hb U) a).1 = canonicalWalkAll U a.1 := rfl

/-- The whole model lies in the original finite homogeneous ambient tree. -/
theorem model_bounded
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Model b l) :
    InHomTree n a.1 :=
  admissible_address_bounded U a.1 (model_admissible hb U a)

/-- Prefix order is both preserved and reflected by the whole model map. -/
theorem model_prefix_iff
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a d : Model b l) :
    IsPrefix a.1 d.1 ↔
      IsPrefix (canonicalWalkAll U a.1) (canonicalWalkAll U d.1) :=
  prefix_realize_iff U ((modelAddressEquiv hb U) a)
    ((modelAddressEquiv hb U) d)

/-- Lexicographic order is both preserved and reflected. -/
theorem model_lex_iff
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a d : Model b l) :
    FinLexLE a.1 d.1 ↔
      FinLexLE (canonicalWalkAll U a.1) (canonicalWalkAll U d.1) :=
  lex_realize_iff U ((modelAddressEquiv hb U) a)
    ((modelAddressEquiv hb U) d)

/-- The corrected forward auxiliary order is both preserved and reflected. -/
theorem model_forwardAux_iff
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a d : Model b l) :
    ForwardAux a.1 d.1 ↔
      ForwardAux (canonicalWalkAll U a.1) (canonicalWalkAll U d.1) :=
  forwardAux_realize_iff U ((modelAddressEquiv hb U) a)
    ((modelAddressEquiv hb U) d)

/-- The model interior is exactly the preimage of the actual interior. -/
theorem model_interior_iff
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Model b l) :
    ModelInterior l a.1 ↔
      canonicalWalkAll U a.1 ∈ SkewTree.interior U.tree := by
  constructor
  · exact canonicalWalkAll_interior hb U a.1
  · intro hint
    exact (modelInterior_iff_interior_address hb U a.1).2
      ⟨(modelAddressEquiv hb U) a, rfl, hint⟩

/-- The model boundary is exactly the preimage of the actual leaves. -/
theorem model_boundary_iff
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Model b l) :
    Definition24Boundary l a.1 ↔
      canonicalWalkAll U a.1 ∉ SkewTree.interior U.tree := by
  constructor
  · intro ha
    exact (boundary_is_leaf hb U ⟨a.1, ha⟩).2
  · exact leaf_address_boundary hb U ((modelAddressEquiv hb U) a)

/-- Root and local successor recursion determine the map on its whole
model, including the singleton model at l=0. -/
theorem canonical_model_unique
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (F : Node b → Node b)
    (hroot : F [] = starredRootAll U)
    (hstep : ∀ p i, ModelInterior l p →
      F (p ++ [i]) = CanonicalSupportWalk.next U.tree (F p) i)
    (a : Model b l) : F a.1 = canonicalWalkAll U a.1 := by
  rcases a.2 with hint | hboundary
  · exact unique_model_map_eq_support_walk hb U.tree (starredRootAll U)
      F hroot hstep a.1 (Or.inl hint)
  · exact canonicalWalkAll_boundary_rigidity hb U F hroot hstep a.1 hboundary

/-- Zero-interior starred supports have exactly one vertex, their own root. -/
theorem zero_vertex_eq_root
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n 0 α
      (SkewTree.forwardAuxB (b := b)))
    (t : Node b) (ht : t ∈ U.tree) : t = starredRootAll U := by
  let a : Model b 0 := (modelVertexEquiv hb U).symm ⟨t, ht⟩
  have ha : a.1 = [] := by
    rcases a.2 with hint | hboundary
    · simp [ModelInterior] at hint
    · exact (definition24Boundary_zero_iff a.1).1 hboundary
  have h := (modelVertexEquiv hb U).apply_symm_apply (⟨t, ht⟩ : Vertex U)
  have hval := congrArg Subtype.val h
  change canonicalWalkAll U a.1 = t at hval
  rw [ha] at hval
  exact hval.symm

end DualTree.ForwardSemiCompleteModelIso
