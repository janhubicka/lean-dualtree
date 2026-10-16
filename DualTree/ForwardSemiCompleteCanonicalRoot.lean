import DualTree.ForwardQCanonicalWalk

/-!
# Intrinsic canonical root and selector on semi-complete starred supports

The published Definition 24 refers to a canonical map I_U on
semi-complete starred trees U, although its preceding definition
introduces I_T for complete trees. This module isolates a natural
finite-source extension that does NOT use the fixed original source root.

For positive interior count, any starred semi-complete U has
a unique support root. We construct it as a choice from the
rootedness predicate, prove independence of that choice, and
define its first-l boundary selector by the genuine finite
support directional walk. On every actual corrected starred
Q output, its intrinsic root is the retained original source
root; therefore the model-A terminal selector agrees with the
previously checked projected D2 point.

Consequently the full original arbitrary-U simplicity predicate,
WHEN interpreted using this explicit intrinsic-root walk,
implies smoothness and a total smooth pullback without any
extra Q-local selector agreement hypothesis.

This is still not a claim that the paper's printed reverse-order
I_U definition equals this proposed positive-l canonical
extension: that source-text alignment must be checked separately.
The l=0 singleton-boundary convention remains tracked in
ForwardCanonicalPartialWalkUniqueness.
-/

namespace DualTree.ForwardSemiCompleteCanonicalRoot

open ForwardSourceQTree
open ForwardQAmbientFibreFrame
open ForwardQAmbientFibreLegalWord
open ForwardQModelBoundaryTransport
open ForwardModelBoundaryHeap

/-- A starred support with a positive number of interior vertices
cannot be a singleton tree: any interior point has an immediate
support successor. -/
theorem starred_nonsingleton
    {b n l : Nat} {α : Type*}
    (hl : 0 < l)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    U.tree.length ≠ 1 := by
  have hpositive : (SkewTree.interior U.tree).length ≠ 0 := by
    rw [U.interior_card]
    omega
  cases hinter : SkewTree.interior U.tree with
  | nil =>
      simp [hinter] at hpositive
  | cons cut rest =>
      have hcut : cut ∈ SkewTree.interior U.tree := by
        simp [hinter]
      have hcutMem : cut ∈ U.tree :=
        (List.mem_filter.mp hcut).1
      cases hsucc : SkewTree.immediateSuccs U.tree cut with
      | nil =>
          have htest := (List.mem_filter.mp hcut).2
          simp [hsucc] at htest
      | cons u us =>
          have huMem : u ∈ SkewTree.immediateSuccs U.tree cut := by
            simp [hsucc]
          have huF : u ∈ U.tree.filter
              (fun t => SkewTree.immediateSuccB U.tree cut t) :=
            huMem
          have huTree : u ∈ U.tree :=
            (List.mem_filter.mp huF).1
          have huStep :
              SkewTree.immediateSuccB U.tree cut u = true :=
            (List.mem_filter.mp huF).2
          have hne : cut ≠ u :=
            ((SkewBranchGeometry.immediateSuccB_iff
              U.tree cut u).1 huStep).2.1.2
          exact SupportReachability.nonsingleton_of_distinct_members
            U.tree hcutMem huTree hne

/-- Every positive-interior semi-complete starred support has a
common prefix root, regardless of its auxiliary source. -/
theorem starred_has_root
    {b n l : Nat} {α : Type*}
    (hl : 0 < l)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    ∃ r : Node b, r ∈ U.tree ∧
      ∀ t, t ∈ U.tree → IsPrefix r t := by
  have hparts := U.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hparts
  have hroot : SkewTree.rootedB U.tree = true :=
    CompleteSkewMeet.rootedB_of_skew_nonSingleton
      SkewTree.forwardAuxB U.tree hparts.1
      (starred_nonsingleton hl U)
  unfold SkewTree.rootedB at hroot
  rcases List.any_eq_true.mp hroot with ⟨r, hr, htest⟩
  refine ⟨r, hr, ?_⟩
  intro t ht
  exact DirectionalSupport.prefix_of_isPrefixOf_true
    ((List.all_eq_true.mp htest) t ht)

/-- Intrinsic root of U. There is no dependency on a
separately fixed original/source root. -/
noncomputable def starredRoot
    {b n l : Nat} {α : Type*}
    (hl : 0 < l)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Node b :=
  Classical.choose (starred_has_root hl U)

theorem starredRoot_mem
    {b n l : Nat} {α : Type*}
    (hl : 0 < l)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    starredRoot hl U ∈ U.tree :=
  (Classical.choose_spec (starred_has_root hl U)).1

theorem starredRoot_prefix
    {b n l : Nat} {α : Type*}
    (hl : 0 < l)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (t : Node b) (ht : t ∈ U.tree) :
    IsPrefix (starredRoot hl U) t :=
  (Classical.choose_spec (starred_has_root hl U)).2 t ht

/-- The root choice is unique and canonical as a tree vertex.
This proof also validates that the noncomputable choice cannot
depend on the enumeration of U.tree. -/
theorem starredRoot_eq_of_common_prefix
    {b n l : Nat} {α : Type*}
    (hl : 0 < l)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (r : Node b) (hr : r ∈ U.tree)
    (hroot : ∀ t, t ∈ U.tree → IsPrefix r t) :
    starredRoot hl U = r :=
  isPrefix_antisymm
    (starredRoot_prefix hl U r hr)
    (hroot (starredRoot hl U) (starredRoot_mem hl U))

/-- Every valid source frame has positive l; this was already
proved by the source-cut heap index and interior cardinality. -/
theorem frame_l_pos
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α) : 0 < l := by
  have hcount := ForwardSourceInteriorFirstL.cut_heapIndex_succ_eq_l hb c
  omega

/-- On an actual finished starred Q output, the UNIQUE intrinsic
root of the output agrees with the original source root.
No externally imposed root convention is needed. -/
theorem starredRoot_actual_Q
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback) :
    starredRoot (frame_l_pos hb c.core)
      (fibreQStarredWord hb c fallback w) =
      ForwardQRooted.sourceRoot c.core := by
  let x := ForwardQEnlargedConstantWords.eraseAux c.core fallback w.1
  let U := fibreQStarredWord hb c fallback w
  have hrootMem : ForwardQRooted.sourceRoot c.core ∈ U.tree := by
    change ForwardQRooted.sourceRoot c.core ∈ (nodes c.core x).toList
    apply Finset.mem_toList.mpr
    exact ForwardQFixedBase.originalInterior_mem_Q c.core x
      (ForwardQRooted.sourceRoot c.core)
      (ForwardQRooted.sourceRoot_interior c.core)
  have hrootPrefix : ∀ t, t ∈ U.tree →
      IsPrefix (ForwardQRooted.sourceRoot c.core) t := by
    intro t ht
    have hq : t ∈ nodes c.core x :=
      Finset.mem_toList.mp (show t ∈ (nodes c.core x).toList from ht)
    exact ForwardQRooted.sourceRoot_prefix_Q c.core x t hq
  exact starredRoot_eq_of_common_prefix
    (frame_l_pos hb c.core) U
    (ForwardQRooted.sourceRoot c.core) hrootMem hrootPrefix

/-- Canonical model-boundary observable using the root of
the STARRED OUTPUT U ITSELF, not a fixed external source root. -/
noncomputable def intrinsicModelPoint
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a : ModelA c) : Node b :=
  CanonicalSupportWalk.walk U.tree
    (starredRoot (frame_l_pos hb c) U) a.1

/-- Rooted walk on every actual Q word agrees with the true
source-relative selector. This is Q-local agreement proved,
not an assumption, for the intrinsic-root interpretation. -/
theorem intrinsicModelPoint_Qlocal
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (a : ModelA c.core) :
    intrinsicModelPoint hb c.core
      (fibreQStarredWord hb c fallback w) a =
    canonicalModelATerminal hb c.core
      (fibreQStarredWord hb c fallback w) a := by
  unfold intrinsicModelPoint
  rw [starredRoot_actual_Q hb c fallback w]
  exact ForwardQCanonicalWalk.modelQWalk_actual_starred_eq_relative_selector
    hb c fallback w a

/-- Any candidate map with the intrinsic support root and
the unique immediate-direction recursion equals the intrinsic
canonical walk on the full Definition 24 boundary. -/
theorem intrinsic_boundary_rigidity
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (hl : 0 < l)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (F : Node b → Node b)
    (hroot : F [] = starredRoot hl U)
    (hstep : ∀ p i, ModelInterior l p →
      F (p ++ [i]) = CanonicalSupportWalk.next U.tree (F p) i)
    (a : Node b)
    (ha : ForwardCanonicalPartialWalkUniqueness.Definition24Boundary l a) :
    F a = CanonicalSupportWalk.walk U.tree (starredRoot hl U) a :=
  ForwardCanonicalPartialWalkUniqueness.unique_definition24_boundary_eq_support_walk
    hb U.tree (starredRoot hl U) F hroot hstep a ha

/-- The ORIGINAL full-ambient arbitrary-U simplicity hypothesis,
interpreted using the actual intrinsic canonical selector,
implies smoothness of the genuine finished Q pullback.
No Q-local comparison premise remains. -/
theorem intrinsic_simple_Q_pullback_smooth
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (B2 : Set (ModelA c.core))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple :
      ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
        c (intrinsicModelPoint hb c.core)
        (fun a => a ∈ B2) color)
    (x y : ForwardQEnlargedConstantWords.EnlargedStarredInput
      c.core fallback)
    (hxy : MixedProduct.SmoothRelated
      (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core
        (markerB2OfModelA hb c.core B2)) x.1 y.1) :
    color (fibreQStarredWord hb c fallback x) =
      color (fibreQStarredWord hb c fallback y) :=
  ForwardQPaperSelectorReduction.paper_simple_Q_pullback_smooth_of_local_agreement
    hb c fallback (intrinsicModelPoint hb c.core)
    B2 color hsimple (intrinsicModelPoint_Qlocal hb c fallback)
    x y hxy

/-- The same intrinsic-selector hypothesis gives the TOTAL
classwise smooth colouring extension over the enlarged product. -/
theorem exists_total_intrinsic_simple_Q_pullback
    {b n l k m : Nat} {α γ : Type*}
    (hb : 0 < b)
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (fallbackColor : γ)
    (B2 : Set (ModelA c.core))
    (color : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) → γ)
    (hsimple :
      ForwardQMarkerTransportInterface.CanonicalSimpleWithinAmbient
        c (intrinsicModelPoint hb c.core)
        (fun a => a ∈ B2) color) :
    ∃ total : ForwardQEnlargedConstantWords.EnlargedInput c.core → γ,
      (∀ w : ForwardQEnlargedConstantWords.EnlargedStarredInput
        c.core fallback,
        total w.1 = color (fibreQStarredWord hb c fallback w)) ∧
      (∀ x y : ForwardQEnlargedConstantWords.EnlargedInput c.core,
        MixedProduct.SmoothRelated
          (ForwardQMarkerSmoothPartition.gamma1OfMarkerB2 c.core
            (markerB2OfModelA hb c.core B2))
          x y → total x = total y) :=
  ForwardQPaperSelectorReduction.exists_total_paper_simple_Q_pullback_of_local_agreement
    hb c fallback fallbackColor
    (intrinsicModelPoint hb c.core)
    B2 color hsimple (intrinsicModelPoint_Qlocal hb c fallback)

end DualTree.ForwardSemiCompleteCanonicalRoot
