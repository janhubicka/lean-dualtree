import DualTree.ForwardSourceQTree
import DualTree.ForwardQAllDirections
import DualTree.ForwardQRooted
import DualTree.CanonicalSupportInjective
import DualTree.SupportReachability

/-!
# Canonical admissible addresses on the actual semi-complete source

The complete-skew support library already proves that a unique
directional-support walk is injective on admissible addresses,
that its intrinsic support rank equals its starting rank plus
the address length, and that every proper support-descendant
has a first immediate successor.

We adapt the remaining SURJECTIVITY step to the actual
semi-complete forward-skew source of corrected Lemma 27:
whenever s is a proper source predecessor of t, it is
interior, and source semi-completeness provides the unique
immediate successor in the direction of t. Recursing by
strictly decreasing ambient length gap gives an admissible
address for EVERY source vertex.

The resulting canonical equivalence identifies:
  { admissible direction words from source root } ≃
  { actual source support vertices }.
The intrinsic rank of a vertex equals its address length.

This does not yet prove the stronger assertion that the
admissible interior addresses are exactly the first l
forward heap addresses; that requires order transport and
the verified source initial-segment condition.
-/

namespace DualTree.ForwardSourceCanonicalAddresses

open ForwardSourceQTree

/-- Every source descendant is reached by a sequence of
unique directional immediate successors, without assuming
the semi-complete source is a k-complete support. -/
theorem source_walk_address_of_prefix
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (s t : Node b)
    (hs : s ∈ c.source.tree)
    (ht : t ∈ c.source.tree)
    (hst : IsPrefix s t) :
    ∃ address : Node b,
      CanonicalSupportWalk.Admissible c.source.tree s address ∧
      CanonicalSupportWalk.walk c.source.tree s address = t := by
  have hmain :
      ∀ d : Nat, ∀ s t : Node b,
        s ∈ c.source.tree → t ∈ c.source.tree →
        IsPrefix s t →
        t.length - s.length = d →
        ∃ address : Node b,
          CanonicalSupportWalk.Admissible c.source.tree s address ∧
          CanonicalSupportWalk.walk c.source.tree s address = t := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro s t hs ht hst hgap
        by_cases heq : s = t
        · subst t
          exact ⟨[], trivial, rfl⟩
        · have hstrict : IsStrictPrefix s t := ⟨hst, heq⟩
          obtain ⟨u, huT, hstep, hsu, hut⟩ :=
            SkewBranchGeometry.exists_first_immediate_on_path
              c.source.tree s t ht hstrict
          obtain ⟨i, hdir⟩ :=
            SupportReachability.first_direction_of_strictPrefix hsu
          have hsInterior : s ∈ SkewTree.interior c.source.tree :=
            SignatureInteriorPersistence.interior_of_strict_descendant
              c.source.tree s t hs ht hstrict
          have hbranch : SkewTree.uniqueBranchB
              c.source.tree s i = true :=
            ForwardQAllDirections.source_full_directions
              c s hsInterior i
          have hnext :
              CanonicalSupportWalk.next c.source.tree s i = u :=
            SupportReachability.next_eq_of_immediate
              c.source.tree s u i hbranch hstep hdir
          have hsmaller : t.length - u.length < d := by
            have hsulen :=
              MeetClosedFromBranching.length_lt_of_strictPrefix hsu
            have hutlen := prefix_length_le hut
            omega
          obtain ⟨tail, hvalid, hwalk⟩ :=
            ih (t.length - u.length) hsmaller
              u t huT ht hut rfl
          refine ⟨i :: tail, ?_, ?_⟩
          · change SkewTree.uniqueBranchB c.source.tree s i = true ∧
                CanonicalSupportWalk.Admissible c.source.tree
                  (CanonicalSupportWalk.next c.source.tree s i) tail
            refine ⟨hbranch, ?_⟩
            rwa [hnext]
          · change CanonicalSupportWalk.walk c.source.tree
                (CanonicalSupportWalk.next c.source.tree s i) tail = t
            simpa [hnext] using hwalk
  exact hmain (t.length - s.length) s t hs ht hst rfl

/-- The canonical source root has an admissible directional
address to EVERY actual source node, of length exactly its
intrinsic support height. -/
theorem source_has_address
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Node b) (ht : t ∈ c.source.tree) :
    ∃ address : Node b,
      CanonicalSupportWalk.Admissible c.source.tree
        (ForwardQRooted.sourceRoot c) address ∧
      CanonicalSupportWalk.walk c.source.tree
        (ForwardQRooted.sourceRoot c) address = t ∧
      address.length = SkewTree.heightAt c.source.tree t := by
  obtain ⟨address, hvalid, hwalk⟩ :=
    source_walk_address_of_prefix c
      (ForwardQRooted.sourceRoot c) t
      (ForwardQRooted.sourceRoot_mem c) ht
      (ForwardQRooted.sourceRoot_prefix c t ht)
  have hparts := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hparts
  have hskew := hparts.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  have hnd : c.source.tree.Nodup := by
    simpa using hskew.1
  have hrank :=
    SupportReachability.walk_height_of_admissible
      c.source.tree hnd address (ForwardQRooted.sourceRoot c)
      (ForwardQRooted.sourceRoot_mem c) hvalid
  have hrootRank :
      SkewTree.heightAt c.source.tree
        (ForwardQRooted.sourceRoot c) = 0 :=
    ImmediateSupportHeight.heightAt_root_zero
      c.source.tree (ForwardQRooted.sourceRoot c)
      (fun v hv => ForwardQRooted.sourceRoot_prefix c v hv)
  have hlen :
      address.length = SkewTree.heightAt c.source.tree t := by
    rw [hwalk, hrootRank] at hrank
    omega
  exact ⟨address, hvalid, hwalk, hlen⟩

/-- Admissible source addresses from the actual rooted source. -/
abbrev SourceAddress
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  {address : Node b //
    CanonicalSupportWalk.Admissible c.source.tree
      (ForwardQRooted.sourceRoot c) address}

/-- Actual source vertices as a finite support subtype. -/
abbrev SourceVertex
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  {s : Node b // s ∈ c.source.tree}

/-- Realize an admissible direction sequence by the literal
unique-successor support walk, not its ambient concatenation. -/
noncomputable def realize
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    SourceAddress c → SourceVertex c :=
  fun u => ⟨CanonicalSupportWalk.walk c.source.tree
    (ForwardQRooted.sourceRoot c) u.1,
    CanonicalSupportWalk.walk_mem_of_admissible
      c.source.tree (ForwardQRooted.sourceRoot c) u.1
      (ForwardQRooted.sourceRoot_mem c) u.2⟩

/-- A directional source address is uniquely determined by
its actual source vertex, even when support edges are stretched. -/
theorem realize_injective
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    Function.Injective (realize c) := by
  intro u v huv
  apply Subtype.ext
  apply CanonicalSupportInjective.walk_injective_of_admissible
    c.source.tree u.1 (ForwardQRooted.sourceRoot c) v.1
    u.2 v.2
  exact congrArg Subtype.val huv

/-- Every source vertex is realized by an admissible
directional address, not just every vertex of the enclosing T. -/
theorem realize_surjective
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    Function.Surjective (realize c) := by
  intro t
  obtain ⟨address, hadm, hwalk, _⟩ :=
    source_has_address c t.1 t.2
  refine ⟨⟨address, hadm⟩, ?_⟩
  apply Subtype.ext
  exact hwalk

/-- Every admissible source address corresponds to exactly
one original source vertex and conversely, for arbitrary
semi-complete source leaf levels. -/
noncomputable def sourceAddressEquiv
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    SourceAddress c ≃ SourceVertex c :=
  Equiv.ofBijective (realize c)
    ⟨realize_injective c, realize_surjective c⟩

end DualTree.ForwardSourceCanonicalAddresses
