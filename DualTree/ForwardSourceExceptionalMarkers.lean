import DualTree.ForwardQLiteralSkeletonMeets
import DualTree.ForwardQInteriorExact
import DualTree.ForwardSignatureInteriorPersistence

/-!
# Exceptional source leaves have distinct first-exit R markers

The forward-corrected signature replaces an exceptional source
terminal t (outside the last interior cut cone) by its first
ambient prefix r outside the strict forward cut.

We prove this replacement is injective on ACTUAL exceptional
source terminals. If two different terminals t,u had the same
boundary r, their ambient meet would be an original source
interior vertex w extending r: meet closure puts w in the source
and terminality forces it to be a strict ancestor of t.
But r lies outside the inclusive forward cut, whereas every
interior vertex w is at/before the cut. Prefix monotonicity
gives a contradiction.

Every actual signature-terminal marker is represented by some
exceptional leaf by the previously checked signature classification.
Together with the cut-child leaf theorem this isolates the
source-leaf-to-R bijection; assembling the two cases and
constructing the canonical first-l model A-to-R map remain open.
-/

namespace DualTree.ForwardSourceExceptionalMarkers

open ForwardSourceQTree
open ForwardSignatureBoundary

/-- The genuine source exceptional leaves, with their
original source tree membership encoded in the subtype. -/
abbrev Exceptional
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  {t : Node b //
    t ∈ StarredSignature.exceptionalLeaves c.source c.cut}

/-- Map a genuine exceptional terminal to its exact first
source-signature boundary under the corrected forward order. -/
noncomputable def exceptionalBoundary
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Exceptional c) : Node b :=
  firstBoundary c.cut t.1 (c.hout t.1 t.2)

/-- The exceptional marker lies on the ambient prefix path
to its actual original source terminal. -/
theorem exceptionalBoundary_prefix
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Exceptional c) :
    IsPrefix (exceptionalBoundary c t) t.1 :=
  (firstBoundary_spec c.cut t.1 (c.hout t.1 t.2)).1

/-- Every chosen exceptional boundary is a member of the
literal corrected source marker set R, not a hypothetical
auxiliary marker family. -/
theorem exceptionalBoundary_mem_literalR
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Exceptional c) :
    exceptionalBoundary c t ∈
      ForwardStarredSignature.literalR
        c.source c.cut c.hout :=
  ForwardQInteriorExact.exceptional_boundary_mem_literalR
    c.source c.cut c.hmax c.hout t

/-- The first-exit marker lies outside the inclusive corrected
auxiliary cut, unlike every original source interior vertex. -/
theorem exceptionalBoundary_outside_cut
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : Exceptional c) :
    ¬ ForwardAux (exceptionalBoundary c t) c.cut :=
  (ForwardSignatureInteriorPersistence.literalR_is_inclusive_boundary
    c.source c.cut c.hcut c.hmax c.hout
    (exceptionalBoundary c t)
    (exceptionalBoundary_mem_literalR c t)).1

/-- Distinct genuine source exceptional terminals cannot
collapse to the same first-exit R marker. This uses source
meet closure and the maximal interior cut, not a cardinality
argument or a guessed branch ordering. -/
theorem exceptionalBoundary_injective
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    Function.Injective (exceptionalBoundary c) := by
  intro t u hsame
  by_cases hval : t.1 = u.1
  · exact Subtype.ext hval
  have htSpec :=
    StarredSignature.exceptionalLeaves_spec
      c.source c.cut t.1 t.2
  have huSpec :=
    StarredSignature.exceptionalLeaves_spec
      c.source c.cut u.1 u.2
  have htS : t.1 ∈ c.source.tree := htSpec.1
  have huS : u.1 ∈ c.source.tree := huSpec.1
  have htLeaf : t.1 ∉ SkewTree.interior c.source.tree :=
    htSpec.2.1
  let w : Node b := MeetGeometry.commonPrefix t.1 u.1
  have hwS : w ∈ c.source.tree :=
    (ForwardQLiteralSkeletonMeets.source_meetClosed c)
      t.1 u.1 htS huS
  have hwt : IsPrefix w t.1 :=
    MeetGeometry.commonPrefix_prefix_left t.1 u.1
  have hwu : IsPrefix w u.1 :=
    MeetGeometry.commonPrefix_prefix_right t.1 u.1
  have hwnot : w ≠ t.1 := by
    intro hw
    have htu : IsPrefix t.1 u.1 := by
      rw [← hw]
      exact hwu
    have htStrict : IsStrictPrefix t.1 u.1 := ⟨htu, hval⟩
    exact htLeaf
      (SignatureInteriorPersistence.interior_of_strict_descendant
        c.source.tree t.1 u.1 htS huS htStrict)
  have hwInterior : w ∈ SkewTree.interior c.source.tree :=
    SignatureInteriorPersistence.interior_of_strict_descendant
      c.source.tree w t.1 hwS htS ⟨hwt, hwnot⟩
  have hwEarly : ForwardAux w c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax w hwInterior
  have hrPrefixW : IsPrefix (exceptionalBoundary c t) w := by
    apply MeetGeometry.prefix_commonPrefix
      (exceptionalBoundary_prefix c t)
    change IsPrefix (exceptionalBoundary c t) u.1
    rw [hsame]
    exact exceptionalBoundary_prefix c u
  have hrEarly : ForwardAux (exceptionalBoundary c t) c.cut :=
    ForwardInclusiveFrontier.forwardAux_of_prefix
      hrPrefixW hwEarly
  exact (exceptionalBoundary_outside_cut c t hrEarly).elim

/-- The source-side signature classification is genuinely
surjective: each actual non-cut signature terminal is the
first-exit boundary of at least one exceptional source leaf.
The previous injectivity theorem shows this preimage is unique. -/
theorem signatureTerminal_has_exceptionalBoundary
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (r : Node b)
    (hr : r ∈
      ForwardStarredSignature.signatureTerminalMarkers
        c.source c.cut c.hout) :
    ∃ t : Exceptional c, exceptionalBoundary c t = r := by
  obtain ⟨t, ht⟩ :=
    ForwardSignatureInteriorPersistence.signatureTerminal_is_exceptional_boundary
      c.source c.cut c.hcut c.hmax c.hout r hr
  exact ⟨t, ht⟩

end DualTree.ForwardSourceExceptionalMarkers
