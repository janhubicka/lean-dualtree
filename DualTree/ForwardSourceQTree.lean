import DualTree.ForwardOrderedProjections
import DualTree.ForwardSortedMixedProduct
import DualTree.ForwardSignatureInteriorPersistence
import DualTree.MixedGood

/-!
# The literal Q tree component under the globally repaired forward order

This is the first *fully source-facing* reconstruction of the tree
component of the corrected Lemma 27 map Q, retaining all its distinct
data: the source starred signature, the final cut t₀, the enclosing
complete skew support T, the sorted frontier coordinates, and the
typed D₀/D₂ mixed-product element.

The formula is unchanged from the printed proof:

  S_x = Int(S') ∪ {t₀} ∪ {P_i(s_i) : i ∈ D₂}.

The repairs are explicit in the types:
* S' and its literal marker set R use the globally forward
  auxiliary cut convention;
* T is genuinely k-complete for *forwardAuxB*;
* the frontier coordinates are sorted in forward auxiliary order;
* the local tail height is the certified safe k-(m+1);
* each P_i is the true forward-complete canonical cone map.

We verify the retained base and projected-node membership,
disjointness of projections from distinct marked coordinates,
the fixed tree skeleton under Gamma₂=D₂ smoothness, and actual
forward/length monotonicity of marked projected nodes whenever
the selected bullet lengths are ordered as required by the
Definition 20 starred domain.

These results do NOT yet establish that the full S_x is a
semi-complete skew support or identify its intrinsic levels.
The word g_x and full colouring compatibility remain separate.
-/

namespace DualTree.ForwardSourceQTree

/-- The complete source-facing parameter package of the corrected
Lemma 27 tree reconstruction. Keeping the input hypotheses in a
structure prevents accidental conflation with the printed-order
canonical map. -/
structure Frame (b n l k m : Nat) (α : Type*) where
  source : StarredSignature.StarredWord b n l α
    (SkewTree.forwardAuxB (b := b))
  cut : Node b
  hcut : cut ∈ SkewTree.interior source.tree
  hmax : ∀ t, t ∈ SkewTree.interior source.tree →
    SkewTree.forwardAuxB t cut = true
  hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves source cut →
    ¬ ForwardSignatureBoundary.BeforeCut cut t
  T : List (Node b)
  hcomplete : SkewTree.completeB SkewTree.forwardAuxB k T = true
  hnon : T.length ≠ 1
  hST : ∀ t, t ∈ source.tree → t ∈ T
  hcutT : cut ∈ T
  hearly : SkewTree.heightAt T cut + 1 < k
  hm : SkewTree.heightAt T cut = m

/-- The corrected mixed-product coordinates, with bullet indices
exactly the image of the literal R marker injection. -/
noncomputable def kind {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    Fin (ForwardSortedFrontiers.frontiers c.T c.cut).length →
      MixedProduct.CoordKind :=
  ForwardSortedMixedProduct.kind
    c.source c.cut c.hcut c.hmax c.hout
    c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly

/-- The honest sorted D₀/D₂ mixed-product domain of the corrected Q. -/
abbrev Input {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  MixedProduct.Element b (k - (m + 1))
    (ForwardSortedFrontiers.frontiers c.T c.cut).length
    α (kind c)

/-- The source's literal old base Int(S') ∪ {t₀},
under the globally forward-repaired signature convention. -/
noncomputable def oldBase {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) : List (Node b) :=
  SkewTree.interior
    (ForwardStarredSignature.signatureTree c.source c.cut c.hout) ++
  [c.cut]

/-- The literal support-valued P_i(s_i) at an actual D₂
coordinate, with corrected sorted frontier and safe tail. -/
noncomputable def markedProjection
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) (i : MixedProduct.BulletIndex (kind c)) :
    {t : Node b // t ∈ c.T} :=
  ForwardUniformConeDomains.projectCommon
    c.T c.hcomplete c.hnon c.cut c.hcutT c.hm
    (ForwardOrderedProjections.frontierAt c.T c.cut i.1)
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut i.1)
    (x.bulletPoint i)

/-- The exact tree component of the corrected source-facing Q:
the retained signature interior and cut, plus all projected
D₂ marker points (not all frontier coordinates). -/
noncomputable def nodes
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) : Finset (Node b) := by
  classical
  exact (oldBase c).toFinset ∪
    (Finset.univ : Finset (MixedProduct.BulletIndex (kind c))).image
      (fun i => (markedProjection c x i).1)

/-- All retained old base vertices belong to the new Q skeleton. -/
theorem oldBase_mem
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) (t : Node b)
    (ht : t ∈ oldBase c) :
    t ∈ nodes c x := by
  classical
  exact Finset.mem_union.mpr
    (Or.inl (List.mem_toFinset.mpr ht))

/-- Every actual D₂ marked point contributes its projected node
to the new Q skeleton. -/
theorem markedProjection_mem
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) (i : MixedProduct.BulletIndex (kind c)) :
    (markedProjection c x i).1 ∈ nodes c x := by
  classical
  apply Finset.mem_union.mpr
  right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- Each source-side projected marker extends its corresponding
unique *sorted* minimal T-frontier. -/
theorem markedProjection_cone
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) (i : MixedProduct.BulletIndex (kind c)) :
    IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1
      (markedProjection c x i).1 :=
  ForwardUniformConeDomains.projectCommon_cone
    c.T c.hcomplete c.hnon c.cut c.hcutT c.hm
    (ForwardOrderedProjections.frontierAt c.T c.cut i.1)
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut i.1)
    (x.bulletPoint i)

/-- Two distinct D₂ coordinates project into incomparable
frontier cones, hence have distinct Q support nodes. -/
theorem markedProjection_injective
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) :
    Function.Injective (markedProjection c x) := by
  intro i j heq
  have hfi :=
    ForwardOrderedProjections.frontierAt_spec c.T c.cut i.1
  have hfj :=
    ForwardOrderedProjections.frontierAt_spec c.T c.cut j.1
  have hpi := markedProjection_cone c x i
  have hpj := markedProjection_cone c x j
  have hpj' :
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1
        (markedProjection c x i).1 := by
    rw [heq]
    exact hpj
  have hfront :
      (ForwardOrderedProjections.frontierAt c.T c.cut i.1).1 =
      (ForwardOrderedProjections.frontierAt c.T c.cut j.1).1 :=
    CutFrontier.frontier_unique_above
      c.T (fun u => ForwardAux u c.cut)
      hfi hfj hpi hpj'
  have hindices : i.1 = j.1 :=
    ForwardOrderedProjections.frontierAt_injective c.T c.cut
      (Subtype.ext hfront)
  exact Subtype.ext hindices

/-- Gamma₂=D₂ smoothness fixes the selected point in every
bullet coordinate, and consequently fixes the entire tree
component of corrected Q (not merely its number of vertices). -/
theorem nodes_eq_of_gamma2_smooth
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x y : Input c)
    (hxy : MixedProduct.SmoothRelated (fun _ => false) x y) :
    nodes c x = nodes c y := by
  have hpoints : ∀ i : MixedProduct.BulletIndex (kind c),
      x.bulletPoint i = y.bulletPoint i := by
    intro i
    exact (hxy.2.2 i).1
  have hproj : ∀ i : MixedProduct.BulletIndex (kind c),
      markedProjection c x i = markedProjection c y i := by
    intro i
    simp only [markedProjection, hpoints i]
  have hfun :
      (fun i : MixedProduct.BulletIndex (kind c) =>
        (markedProjection c x i).1) =
      (fun i : MixedProduct.BulletIndex (kind c) =>
        (markedProjection c y i).1) := by
    funext i
    exact congrArg Subtype.val (hproj i)
  unfold nodes
  rw [hfun]

/-- The actual reconstructed marked nodes are forward-ordered
when the selected local D₂ point lengths satisfy the exact
starred-domain monotonicity. This uses genuine T-rank increments
and the sorted frontier coordinate enumeration. -/
theorem markedProjection_forward_order
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i j : MixedProduct.BulletIndex (kind c))
    (hij : i.1 < j.1)
    (hlength :
      (x.bulletPoint i).1.length ≤ (x.bulletPoint j).1.length) :
    ForwardAux
      (markedProjection c x i).1
      (markedProjection c x j).1 := by
  have hc := c.hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  let f := ForwardOrderedProjections.frontierAt c.T c.cut i.1
  let g := ForwardOrderedProjections.frontierAt c.T c.cut j.1
  let u := markedProjection c x i
  let v := markedProjection c x j
  have hne : f.1 ≠ g.1 := by
    intro heq
    have hindex : i.1 = j.1 :=
      ForwardOrderedProjections.frontierAt_injective
        c.T c.cut (Subtype.ext heq)
    exact (ne_of_lt hij) hindex
  have hfg : ForwardAux f.1 g.1 :=
    ForwardSortedFrontiers.frontiers_get_order
      c.T c.cut i.1 j.1 hij
  exact ForwardProjectedTerminalOrder.ordered_frontier_projections_forwardAux
    c.T hc.1 c.hnon c.cut f.1 g.1 u.1 v.1
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut i.1)
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut j.1)
    hne hfg u.2 v.2
    (markedProjection_cone c x i)
    (markedProjection_cone c x j)
    (x.bulletPoint i).1.length
    (x.bulletPoint j).1.length
    (ForwardUniformConeDomains.projectCommon_height
      c.T c.hcomplete c.hnon c.cut c.hcutT c.hm f
      (ForwardOrderedProjections.frontierAt_spec c.T c.cut i.1)
      (x.bulletPoint i))
    (ForwardUniformConeDomains.projectCommon_height
      c.T c.hcomplete c.hnon c.cut c.hcutT c.hm g
      (ForwardOrderedProjections.frontierAt_spec c.T c.cut j.1)
      (x.bulletPoint j))
    hlength

/-- The marked-to-marked ambient length part of skew clause
(ii) follows for the literal forward Q reconstruction. -/
theorem markedProjection_length_le
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i j : MixedProduct.BulletIndex (kind c))
    (hij : i.1 < j.1)
    (hlength :
      (x.bulletPoint i).1.length ≤ (x.bulletPoint j).1.length) :
    (markedProjection c x i).1.length ≤
      (markedProjection c x j).1.length := by
  rcases markedProjection_forward_order c x i j hij hlength with
    hlt | ⟨heq, _⟩
  · omega
  · omega

end DualTree.ForwardSourceQTree
