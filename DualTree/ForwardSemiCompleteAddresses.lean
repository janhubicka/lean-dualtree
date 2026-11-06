import DualTree.ForwardSemiCompleteZeroRoot
import DualTree.CanonicalSupportInjective
import DualTree.SupportReachability

/-!
# Canonical addresses on arbitrary semi-complete starred supports

The semi-complete selector in Definition 24 is used on every eligible
starred support, not only on outputs of the corrected Q construction.
This module constructs the address-to-vertex equivalence directly from
the starred support's own root and unique directional successors.

No surrounding complete tree, signature cut, or Q frame is required.
The result includes zero-interior supports: the root still supplies the
empty admissible address. Every admissible walk has intrinsic height
equal to its address length, and every support vertex has such an address.
-/

namespace DualTree.ForwardSemiCompleteAddresses

open ForwardSemiCompleteZeroRoot

/-- A starred support is stored without repetitions. -/
theorem support_nodup
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    U.tree.Nodup := by
  have hparts := U.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hparts
  have hskew := hparts.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  simpa using hskew.1

/-- Every interior point of an arbitrary semi-complete starred
support has its unique support successor in each ambient direction. -/
theorem full_directions
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (s : Node b) (hs : s ∈ SkewTree.interior U.tree)
    (i : Fin b) :
    SkewTree.uniqueBranchB U.tree s i = true := by
  have hsU : s ∈ U.tree := (List.mem_filter.mp hs).1
  have hl : 0 < l := by
    have hlen : 0 < (SkewTree.interior U.tree).length :=
      List.length_pos_of_mem hs
    rwa [U.interior_card] at hlen
  have hnonleaf : (SkewTree.immediateSuccs U.tree s).length ≠ 0 := by
    have htest := (List.mem_filter.mp hs).2
    cases hlist : SkewTree.immediateSuccs U.tree s with
    | nil => simp [hlist] at htest
    | cons u us => simp [hlist]
  have htotal :
      ∀ s t : Node b, s ≠ t →
        SkewTree.forwardAuxB s t = true ∨
        SkewTree.forwardAuxB t s = true := by
    intro u v _
    rcases CanonicalForwardAuxIso.forwardAux_total u v with h | h
    · exact Or.inl (by simpa [SkewTree.forwardAuxB] using h)
    · exact Or.inr (by simpa [SkewTree.forwardAuxB] using h)
  exact SemiCompleteSkewMeet.fullDirections_of_semiComplete_nonleaf_total
    SkewTree.forwardAuxB U.tree U.semi_complete
    (ForwardSemiCompleteCanonicalRoot.starred_nonsingleton hl U)
    htotal s hsU hnonleaf i

/-- Every support descendant is reached by a finite admissible
directional walk, even when different leaves have different heights. -/
theorem walk_address_of_prefix
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (s t : Node b)
    (hs : s ∈ U.tree) (ht : t ∈ U.tree)
    (hst : IsPrefix s t) :
    ∃ address : Node b,
      CanonicalSupportWalk.Admissible U.tree s address ∧
      CanonicalSupportWalk.walk U.tree s address = t := by
  have hmain :
      ∀ d : Nat, ∀ s t : Node b,
        s ∈ U.tree → t ∈ U.tree → IsPrefix s t →
        t.length - s.length = d →
        ∃ address : Node b,
          CanonicalSupportWalk.Admissible U.tree s address ∧
          CanonicalSupportWalk.walk U.tree s address = t := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro s t hs ht hst hgap
        by_cases heq : s = t
        · subst t
          exact ⟨[], trivial, rfl⟩
        · have hstrict : IsStrictPrefix s t := ⟨hst, heq⟩
          obtain ⟨u, huU, hstep, hsu, hut⟩ :=
            SkewBranchGeometry.exists_first_immediate_on_path
              U.tree s t ht hstrict
          obtain ⟨i, hdir⟩ :=
            SupportReachability.first_direction_of_strictPrefix hsu
          have hsInterior : s ∈ SkewTree.interior U.tree :=
            SignatureInteriorPersistence.interior_of_strict_descendant
              U.tree s t hs ht hstrict
          have hbranch : SkewTree.uniqueBranchB U.tree s i = true :=
            full_directions U s hsInterior i
          have hnext : CanonicalSupportWalk.next U.tree s i = u :=
            SupportReachability.next_eq_of_immediate
              U.tree s u i hbranch hstep hdir
          have hsmaller : t.length - u.length < d := by
            have hsulen :=
              MeetClosedFromBranching.length_lt_of_strictPrefix hsu
            have hutlen := prefix_length_le hut
            omega
          obtain ⟨tail, hvalid, hwalk⟩ :=
            ih (t.length - u.length) hsmaller u t huU ht hut rfl
          refine ⟨i :: tail, ?_, ?_⟩
          · change SkewTree.uniqueBranchB U.tree s i = true ∧
                CanonicalSupportWalk.Admissible U.tree
                  (CanonicalSupportWalk.next U.tree s i) tail
            refine ⟨hbranch, ?_⟩
            rwa [hnext]
          · change CanonicalSupportWalk.walk U.tree
                (CanonicalSupportWalk.next U.tree s i) tail = t
            simpa [hnext] using hwalk
  exact hmain (t.length - s.length) s t hs ht hst rfl

/-- Every support vertex has an admissible address from the
intrinsic root, of length exactly its intrinsic support height. -/
theorem has_address
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (t : Node b) (ht : t ∈ U.tree) :
    ∃ address : Node b,
      CanonicalSupportWalk.Admissible U.tree (starredRootAll U) address ∧
      canonicalWalkAll U address = t ∧
      address.length = SkewTree.heightAt U.tree t := by
  obtain ⟨address, hvalid, hwalk⟩ :=
    walk_address_of_prefix U (starredRootAll U) t
      (starredRootAll_mem U) ht (starredRootAll_prefix U t ht)
  have hrank := SupportReachability.walk_height_of_admissible
    U.tree (support_nodup U) address (starredRootAll U)
    (starredRootAll_mem U) hvalid
  have hrootRank : SkewTree.heightAt U.tree (starredRootAll U) = 0 :=
    ImmediateSupportHeight.heightAt_root_zero U.tree (starredRootAll U)
      (fun v hv => starredRootAll_prefix U v hv)
  refine ⟨address, hvalid, hwalk, ?_⟩
  rw [hwalk, hrootRank] at hrank
  omega

/-- Admissible directional addresses from the starred support's root. -/
abbrev Address
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :=
  {a : Node b // CanonicalSupportWalk.Admissible U.tree (starredRootAll U) a}

/-- Vertices of the actual starred support. -/
abbrev Vertex
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :=
  {s : Node b // s ∈ U.tree}

/-- Realize an admissible address by the intrinsic directional walk. -/
noncomputable def realize
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Address U → Vertex U :=
  fun a => ⟨canonicalWalkAll U a.1,
    CanonicalSupportWalk.walk_mem_of_admissible
      U.tree (starredRootAll U) a.1 (starredRootAll_mem U) a.2⟩

/-- Distinct admissible addresses have distinct support values. -/
theorem realize_injective
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    Function.Injective (realize U) := by
  intro a d had
  apply Subtype.ext
  apply CanonicalSupportInjective.walk_injective_of_admissible
    U.tree a.1 (starredRootAll U) d.1 a.2 d.2
  exact congrArg Subtype.val had

/-- Every actual support vertex is realized. -/
theorem realize_surjective
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    Function.Surjective (realize U) := by
  intro t
  obtain ⟨a, hadm, hwalk, _⟩ := has_address U t.1 t.2
  exact ⟨⟨a, hadm⟩, Subtype.ext hwalk⟩

/-- Canonical addresses give a bijection with every arbitrary
semi-complete starred support, with no complete-tree parameter. -/
noncomputable def addressEquiv
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Address U ≃ Vertex U :=
  Equiv.ofBijective (realize U)
    ⟨realize_injective U, realize_surjective U⟩

@[simp] theorem addressEquiv_apply
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Address U) :
    (addressEquiv U) a = realize U a := rfl

/-- Address length is exactly the intrinsic height of its image. -/
theorem height_realize_eq_length
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Address U) :
    SkewTree.heightAt U.tree (realize U a).1 = a.1.length := by
  have hwalk := SupportReachability.walk_height_of_admissible
    U.tree (support_nodup U) a.1 (starredRootAll U)
    (starredRootAll_mem U) a.2
  have hroot : SkewTree.heightAt U.tree (starredRootAll U) = 0 :=
    ImmediateSupportHeight.heightAt_root_zero U.tree (starredRootAll U)
      (fun v hv => starredRootAll_prefix U v hv)
  change SkewTree.heightAt U.tree
      (CanonicalSupportWalk.walk U.tree (starredRootAll U) a.1) = a.1.length
  rw [hwalk, hroot]
  omega

/-- Every admissible direction advances by at least one ambient level. -/
theorem length_add_le_walk_length
    {b : Nat} (T : List (Node b)) :
    ∀ (a s : Node b), CanonicalSupportWalk.Admissible T s a →
      s.length + a.length ≤ (CanonicalSupportWalk.walk T s a).length := by
  intro a
  induction a with
  | nil =>
      intro s _
      simp [CanonicalSupportWalk.walk]
  | cons i tail ih =>
      intro s ha
      have hstep := prefix_length_le
        (CanonicalSupportWalk.next_unique T s i ha.1).2
      have htail := ih (CanonicalSupportWalk.next T s i) ha.2
      change s.length + (i :: tail).length ≤
        (CanonicalSupportWalk.walk T (CanonicalSupportWalk.next T s i) tail).length
      simp only [List.length_append, List.length_singleton] at hstep
      simp only [List.length_cons]
      omega

/-- The homogeneous address cannot be longer than its ambient image. -/
theorem address_length_le_image_length
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Address U) :
    a.1.length ≤ (realize U a).1.length := by
  have h := length_add_le_walk_length U.tree a.1 (starredRootAll U) a.2
  change a.1.length ≤
    (CanonicalSupportWalk.walk U.tree (starredRootAll U) a.1).length
  omega

/-- The canonical address lies in the same finite homogeneous ambient
tree as its image. This validates the finite-domain restriction in
Definition 24, once admissibility of its model boundary is established. -/
theorem admissible_address_bounded
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a : Node b)
    (ha : CanonicalSupportWalk.Admissible U.tree (starredRootAll U) a) :
    InHomTree n a := by
  let u : Address U := ⟨a, ha⟩
  exact lt_of_le_of_lt (address_length_le_image_length U u)
    (U.tree_bounded (realize U u).1 (realize U u).2)

end DualTree.ForwardSemiCompleteAddresses
