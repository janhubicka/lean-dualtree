import DualTree.ForwardSemiCompleteModelIso
import DualTree.ForwardSemiCompleteSimplicity

/-!
# Canonical selectors do not depend on support enumeration

The corrected Definition 24 selector is an intrinsic directional walk on
a genuine semi-complete starred support.  Q coverage may re-enumerate that
support, so literal list equality is too strong for transporting its
boundary points.

Immediate-support succession depends only on membership in the support.
On an admissible path each directional successor is unique, and hence
the selected successor is unchanged by re-enumeration.  Together with
uniqueness of the intrinsic root, this proves invariance of the canonical
map on the whole model and of every canonical boundary point under
finite-set equality.  The exceptional zero-interior boundary is included.

The result is restricted to admissible paths.  The totalized walk on an
arbitrary invalid path can select the first of several branch witnesses,
so no enumeration-invariance assertion is made for such paths.
-/

namespace DualTree.CanonicalPointReenumeration

open ForwardSemiCompleteZeroRoot
open ForwardSemiCompleteSimplicity

private theorem immediateSucc_iff_of_mem_iff
    {b : Nat} (S T : List (Node b))
    (hmem : ∀ t : Node b, t ∈ S ↔ t ∈ T) (s t : Node b) :
    SkewTree.immediateSuccB S s t = true ↔
      SkewTree.immediateSuccB T s t = true := by
  rw [SkewBranchGeometry.immediateSuccB_iff,
    SkewBranchGeometry.immediateSuccB_iff]
  constructor
  · rintro ⟨ht, hst, hno⟩
    exact ⟨(hmem t).1 ht, hst,
      fun u hu => hno u ((hmem u).2 hu)⟩
  · rintro ⟨ht, hst, hno⟩
    exact ⟨(hmem t).2 ht, hst,
      fun u hu => hno u ((hmem u).1 hu)⟩

private theorem next_eq_of_unique_mem_iff
    {b : Nat} (S T : List (Node b))
    (hmem : ∀ t : Node b, t ∈ S ↔ t ∈ T)
    (s : Node b) (i : Fin b)
    (hS : SkewTree.uniqueBranchB S s i = true)
    (hT : SkewTree.uniqueBranchB T s i = true) :
    CanonicalSupportWalk.next S s i =
      CanonicalSupportWalk.next T s i := by
  have hs := CanonicalSupportWalk.next_unique S s i hS
  have ht := CanonicalSupportWalk.next_unique T s i hT
  apply SkewBranchGeometry.eq_of_mem_uniqueBranch S s i hS
  · exact (SkewBranchGeometry.mem_branchWitnesses_iff S s _ i).2 hs
  · apply (SkewBranchGeometry.mem_branchWitnesses_iff S s _ i).2
    exact ⟨(immediateSucc_iff_of_mem_iff S T hmem s _).2 ht.1, ht.2⟩

private theorem walk_eq_of_admissible_mem_iff
    {b : Nat} (S T : List (Node b))
    (hmem : ∀ t : Node b, t ∈ S ↔ t ∈ T)
    (root a : Node b)
    (hS : CanonicalSupportWalk.Admissible S root a)
    (hT : CanonicalSupportWalk.Admissible T root a) :
    CanonicalSupportWalk.walk S root a =
      CanonicalSupportWalk.walk T root a := by
  induction a generalizing root with
  | nil => rfl
  | cons i tail ih =>
      rcases hS with ⟨hSnext, hStail⟩
      rcases hT with ⟨hTnext, hTtail⟩
      have hnext := next_eq_of_unique_mem_iff S T hmem root i hSnext hTnext
      change CanonicalSupportWalk.walk S
        (CanonicalSupportWalk.next S root i) tail =
          CanonicalSupportWalk.walk T
            (CanonicalSupportWalk.next T root i) tail
      rw [← hnext] at hTtail ⊢
      exact ih (CanonicalSupportWalk.next S root i) hStail hTtail

variable {b n l : Nat} {α : Type*}

/-- The unique common prefix root depends on the support set, for every
interior count, independently of its enumeration and accompanying word. -/
theorem starredRootAll_eq_of_mem_iff
    (U V : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hmem : ∀ t : Node b, t ∈ U.tree ↔ t ∈ V.tree) :
    starredRootAll U = starredRootAll V := by
  apply isPrefix_antisymm
  · exact starredRootAll_prefix U (starredRootAll V)
      ((hmem _).2 (starredRootAll_mem V))
  · exact starredRootAll_prefix V (starredRootAll U)
      ((hmem _).1 (starredRootAll_mem U))

/-- On the entire intrinsic model, the canonical maps agree whenever the
two genuine starred supports have the same members. -/
theorem canonicalWalkAll_model_eq_of_mem_iff
    (hb : 0 < b)
    (U V : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hmem : ∀ t : Node b, t ∈ U.tree ↔ t ∈ V.tree)
    (a : ForwardSemiCompleteModelIso.Model b l) :
    canonicalWalkAll U a.1 = canonicalWalkAll V a.1 := by
  have hU := ForwardSemiCompleteModelIso.model_admissible hb U a
  have hV := ForwardSemiCompleteModelIso.model_admissible hb V a
  have hroot := starredRootAll_eq_of_mem_iff U V hmem
  unfold canonicalWalkAll
  rw [← hroot] at hV ⊢
  exact walk_eq_of_admissible_mem_iff U.tree V.tree hmem
    (starredRootAll U) a.1 hU hV

/-- Canonical Definition 24 boundary points are invariant under any
membership-preserving change of support enumeration, including l = 0. -/
theorem canonicalPoint_eq_of_mem_iff
    (hb : 0 < b)
    (U V : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (hmem : ∀ t : Node b, t ∈ U.tree ↔ t ∈ V.tree)
    (a : Boundary b l) :
    canonicalPoint U a = canonicalPoint V a :=
  canonicalWalkAll_model_eq_of_mem_iff hb U V hmem ⟨a.1, Or.inr a.2⟩

/-- Equality of the actual support finite sets suffices for transporting
every canonical boundary point through a re-enumerated Q preimage. -/
theorem canonicalPoint_eq_of_tree_toFinset_eq
    (hb : 0 < b)
    (U V : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (h : U.tree.toFinset = V.tree.toFinset)
    (a : Boundary b l) :
    canonicalPoint U a = canonicalPoint V a := by
  apply canonicalPoint_eq_of_mem_iff hb U V _ a
  intro t
  have ht : t ∈ U.tree.toFinset ↔ t ∈ V.tree.toFinset := by rw [h]
  simpa only [List.mem_toFinset] using ht

end DualTree.CanonicalPointReenumeration
