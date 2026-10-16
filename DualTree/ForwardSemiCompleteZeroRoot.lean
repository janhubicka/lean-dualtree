import DualTree.ForwardQPaperSelectorRecursion

/-!
# Uniform intrinsic support root, including Definition 24's l=0 case

For l>0 the verified intrinsic-root construction uses the existence
of an interior source vertex to rule out singleton supports.
Definition 24 also has an exceptional case l=0 where its boundary
is the singleton {empty address}. That case still has to choose
the unique root of the starred support itself.

Every semi-complete starred support, regardless of interior count,
has a unique common prefix root:
  * for a singleton tree, its only vertex is the root;
  * otherwise its skew axioms imply rootedB.
This module packages a single root choice for all l, compares it
with the already validated positive-interior intrinsic root, and
proves that Definition 24's A_0 selector evaluates to this root.
The finite root/step uniqueness theorem now has a uniform all-l
intrinsic-root formulation.

No reverse-lex W_* domain, mixed span/Hall or Ramsey iteration
is silently assumed. The paper still must explicitly identify its
semi-complete I_U with this unambiguous directional walk.
-/

namespace DualTree.ForwardSemiCompleteZeroRoot

open ForwardSemiCompleteCanonicalRoot
open ForwardModelBoundaryHeap

/-- Every finite semi-complete starred support has a root,
even when its number of interior nodes is zero. -/
theorem starred_has_root_all
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    ∃ r : Node b, r ∈ U.tree ∧
      ∀ t, t ∈ U.tree → IsPrefix r t := by
  have hparts := U.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hparts
  by_cases hsingle : U.tree.length = 1
  · cases htree : U.tree with
    | nil =>
        simp [htree] at hsingle
    | cons r rest =>
        cases rest with
        | nil =>
            refine ⟨r, by simp [htree], ?_⟩
            intro t ht
            have htr : t = r := by
              simpa [htree] using ht
            subst t
            exact isPrefix_refl r
        | cons s ss =>
            simp [htree] at hsingle
  · have hroot : SkewTree.rootedB U.tree = true :=
      CompleteSkewMeet.rootedB_of_skew_nonSingleton
        SkewTree.forwardAuxB U.tree hparts.1 hsingle
    unfold SkewTree.rootedB at hroot
    rcases List.any_eq_true.mp hroot with ⟨r, hr, htest⟩
    refine ⟨r, hr, ?_⟩
    intro t ht
    exact DirectionalSupport.prefix_of_isPrefixOf_true
      ((List.all_eq_true.mp htest) t ht)

/-- Intrinsic support root valid for all interior counts,
including the singleton model boundary A_0. -/
noncomputable def starredRootAll
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) : Node b :=
  Classical.choose (starred_has_root_all U)

theorem starredRootAll_mem
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    starredRootAll U ∈ U.tree :=
  (Classical.choose_spec (starred_has_root_all U)).1

theorem starredRootAll_prefix
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (t : Node b) (ht : t ∈ U.tree) :
    IsPrefix (starredRootAll U) t :=
  (Classical.choose_spec (starred_has_root_all U)).2 t ht

/-- The uniform root agrees with the already checked
positive-l intrinsic root, by uniqueness of common support roots. -/
theorem starredRootAll_eq_positive
    {b n l : Nat} {α : Type*}
    (hl : 0 < l)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) :
    starredRootAll U = starredRoot hl U :=
  isPrefix_antisymm
    (starredRootAll_prefix U (starredRoot hl U)
      (starredRoot_mem hl U))
    (starredRoot_prefix hl U (starredRootAll U)
      (starredRootAll_mem U))

/-- The canonical all-l semi-complete support walk,
independently of any ambient source or auxiliary root. -/
noncomputable def canonicalWalkAll
    {b n l : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b))) (a : Node b) : Node b :=
  CanonicalSupportWalk.walk U.tree (starredRootAll U) a

/-- At positive interior count the uniform canonical map
is EXACTLY the already audited intrinsic-root walk. -/
theorem canonicalWalkAll_eq_positive
    {b n l : Nat} {α : Type*}
    (hl : 0 < l)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (a : Node b) :
    canonicalWalkAll U a =
      CanonicalSupportWalk.walk U.tree (starredRoot hl U) a := by
  unfold canonicalWalkAll
  rw [starredRootAll_eq_positive hl U]

/-- Definition 24's exceptional A_0={[]} maps precisely to
the intrinsic root. This handles the zero-interior boundary
WITHOUT pretending it is an external child of an empty model. -/
theorem canonicalWalkAll_zero_boundary
    {b n : Nat} {α : Type*}
    (U : StarredSignature.StarredWord b n 0 α
      (SkewTree.forwardAuxB (b := b)))
    (a : Node b)
    (ha : ForwardCanonicalPartialWalkUniqueness.Definition24Boundary
      0 a) :
    canonicalWalkAll U a = starredRootAll U := by
  have hzero : a = [] :=
    (ForwardCanonicalPartialWalkUniqueness.definition24Boundary_zero_iff a).mp ha
  subst a
  rfl

/-- For every l including zero, root and local
finite-support successor recursion force any proposed
paper canonical map to agree on its entire Definition 24
boundary with the uniform intrinsic-root walk. -/
theorem canonicalWalkAll_boundary_rigidity
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (U : StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)))
    (F : Node b → Node b)
    (hroot : F [] = starredRootAll U)
    (hstep : ∀ p i, ModelInterior l p →
      F (p ++ [i]) = CanonicalSupportWalk.next U.tree (F p) i)
    (a : Node b)
    (ha : ForwardCanonicalPartialWalkUniqueness.Definition24Boundary
      l a) :
    F a = canonicalWalkAll U a := by
  exact
    ForwardCanonicalPartialWalkUniqueness.unique_definition24_boundary_eq_support_walk
      hb U.tree (starredRootAll U) F
      hroot hstep a ha

end DualTree.ForwardSemiCompleteZeroRoot
