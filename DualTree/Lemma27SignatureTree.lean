import DualTree.ConeLocalPatchSmoothness
import DualTree.UniformConeDomains
import DualTree.LiteralMarkerCoordinates

/-!
# The tree component of the source's Lemma 27 map Q

On page 28, the printed map Q sends a mixed-product element x to
a starred object (S_x, g_x), where the tree component is

  S_x = Int(S') ∪ {t₀} ∪ {P_i(s_i) : i ∈ D₂}.

This module defines that tree *as a finite set of ambient nodes*,
using the actual list of minimal support frontiers, the actual
canonical maps P_i on a certified common local domain, and the
mixed-product's typed bullet indices.

It proves that distinct bullet coordinates project into disjoint
frontier cones, so no two of the newly marked nodes collide.
It also verifies that S_x is invariant under the Gamma₂=D₂
instance of Definition 21 smoothness, which fixes the bullet points.

This is not a construction of the starred word g_x, nor a proof
that S_x is semi-complete with the prescribed interior. Those two
substantive obligations and the other Gamma₁/Gamma₂ cases remain open.
-/

namespace DualTree.Lemma27SignatureTree

/-- The indexed minimal outside-cut frontier, viewed as a support node. -/
noncomputable def frontierAt {b : Nat}
    (T : List (Node b)) (cut : Node b)
    (i : Fin (LiteralFrontierCount.frontiers T cut).length) :
    {t : Node b // t ∈ T} := by
  let f := (LiteralFrontierCount.frontiers T cut).get i
  have hf : CutFrontier.Frontier T (fun u => PaperAux u cut) f :=
    (LiteralFrontierCount.mem_frontiers_iff T cut f).1
      (List.get_mem (LiteralFrontierCount.frontiers T cut) i)
  exact ⟨f, hf.1⟩

/-- The indexed node really is one of the minimal outside-cut frontiers. -/
theorem frontierAt_spec {b : Nat}
    (T : List (Node b)) (cut : Node b)
    (i : Fin (LiteralFrontierCount.frontiers T cut).length) :
    CutFrontier.Frontier T (fun u => PaperAux u cut)
      (frontierAt T cut i).1 := by
  exact (LiteralFrontierCount.mem_frontiers_iff T cut _).1
    (List.get_mem (LiteralFrontierCount.frontiers T cut) i)

/-- Project the marked local point at one D₂ coordinate through the
actual complete-skew canonical map rooted at its indexed frontier. -/
noncomputable def markedProjection {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    {kind : Fin (LiteralFrontierCount.frontiers T cut).length →
      MixedProduct.CoordKind}
    {α : Type*}
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α kind)
    (i : MixedProduct.BulletIndex kind) :
    {t : Node b // t ∈ T} :=
  UniformConeDomains.projectCommon T hcomplete cut hcut hlevel hm
    (frontierAt T cut i.1) (frontierAt_spec T cut i.1)
    (x.bulletPoint i)

/-- Each new marked node extends its corresponding support frontier. -/
theorem markedProjection_frontier_prefix {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    {kind : Fin (LiteralFrontierCount.frontiers T cut).length →
      MixedProduct.CoordKind}
    {α : Type*}
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α kind)
    (i : MixedProduct.BulletIndex kind) :
    IsPrefix (frontierAt T cut i.1).1
      (markedProjection T hcomplete cut hcut hlevel hm x i).1 :=
  UniformConeDomains.projectCommon_cone T hcomplete cut hcut hlevel hm
    (frontierAt T cut i.1) (frontierAt_spec T cut i.1)
    (x.bulletPoint i)

/-- Marked points in different D₂ coordinates never collide:
different minimal frontiers have disjoint successor cones. -/
theorem markedProjection_injective {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    {kind : Fin (LiteralFrontierCount.frontiers T cut).length →
      MixedProduct.CoordKind}
    {α : Type*}
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α kind) :
    Function.Injective
      (markedProjection T hcomplete cut hcut hlevel hm x) := by
  intro i j hij
  have hfi := frontierAt_spec T cut i.1
  have hfj := frontierAt_spec T cut j.1
  have hpi := markedProjection_frontier_prefix
    T hcomplete cut hcut hlevel hm x i
  have hpj := markedProjection_frontier_prefix
    T hcomplete cut hcut hlevel hm x j
  have hpj' :
      IsPrefix (frontierAt T cut j.1).1
        (markedProjection T hcomplete cut hcut hlevel hm x i).1 := by
    rw [hij]
    exact hpj
  have hfront :
      (frontierAt T cut i.1).1 = (frontierAt T cut j.1).1 :=
    CutFrontier.frontier_unique_above T (fun t => PaperAux t cut)
      hfi hfj hpi hpj'
  let F := LiteralFrontierCount.frontiers T cut
  have hget : F.get i.1 = F.get j.1 := by
    simpa [F, frontierAt] using hfront
  have hequiv :
      (List.Nodup.getEquiv F
        (LiteralFrontierCount.frontiers_nodup T cut)) i.1 =
      (List.Nodup.getEquiv F
        (LiteralFrontierCount.frontiers_nodup T cut)) j.1 :=
    Subtype.ext hget
  have hidx : i.1 = j.1 :=
    (List.Nodup.getEquiv F
      (LiteralFrontierCount.frontiers_nodup T cut)).injective hequiv
  exact Subtype.ext hidx

/-- The complete finite tree skeleton from Q, parameterised by the
old signature nodes which must be retained. -/
noncomputable def signatureNodes {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    {kind : Fin (LiteralFrontierCount.frontiers T cut).length →
      MixedProduct.CoordKind}
    {α : Type*}
    (base : List (Node b))
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α kind) :
    Finset (Node b) := by
  classical
  exact base.toFinset ∪
    (Finset.univ : Finset (MixedProduct.BulletIndex kind)).image
      (fun i => (markedProjection T hcomplete cut hcut hlevel hm x i).1)

/-- The old signature skeleton stays in every Q tree component. -/
theorem signatureNodes_base {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    {kind : Fin (LiteralFrontierCount.frontiers T cut).length →
      MixedProduct.CoordKind}
    {α : Type*}
    (base : List (Node b))
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α kind)
    (s : Node b) (hs : s ∈ base) :
    s ∈ signatureNodes T hcomplete cut hcut hlevel hm base x := by
  classical
  exact Finset.mem_union.mpr
    (Or.inl (List.mem_toFinset.mpr hs))

/-- Each projected marked point belongs to the Q tree component. -/
theorem signatureNodes_marked {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    {kind : Fin (LiteralFrontierCount.frontiers T cut).length →
      MixedProduct.CoordKind}
    {α : Type*}
    (base : List (Node b))
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α kind)
    (i : MixedProduct.BulletIndex kind) :
    (markedProjection T hcomplete cut hcut hlevel hm x i).1 ∈
      signatureNodes T hcomplete cut hcut hlevel hm base x := by
  classical
  apply Finset.mem_union.mpr
  right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- Gamma₂=D₂ smoothness fixes all bullet points, so it fixes the
entire tree component of Q, not merely its cardinality. -/
theorem signatureNodes_eq_of_gamma2_smooth {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    {kind : Fin (LiteralFrontierCount.frontiers T cut).length →
      MixedProduct.CoordKind}
    {α : Type*}
    (base : List (Node b))
    (x y : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α kind)
    (hxy : MixedProduct.SmoothRelated (fun _ => false) x y) :
    signatureNodes T hcomplete cut hcut hlevel hm base x =
      signatureNodes T hcomplete cut hcut hlevel hm base y := by
  classical
  have hpoints : ∀ i : MixedProduct.BulletIndex kind,
      x.bulletPoint i = y.bulletPoint i := by
    intro i
    exact (hxy.2.2 i).1
  have hproj : ∀ i : MixedProduct.BulletIndex kind,
      markedProjection T hcomplete cut hcut hlevel hm x i =
        markedProjection T hcomplete cut hcut hlevel hm y i := by
    intro i
    rw [hpoints i]
  have hfun :
      (fun i : MixedProduct.BulletIndex kind =>
        (markedProjection T hcomplete cut hcut hlevel hm x i).1) =
      (fun i : MixedProduct.BulletIndex kind =>
        (markedProjection T hcomplete cut hcut hlevel hm y i).1) := by
    funext i
    exact congrArg Subtype.val (hproj i)
  unfold signatureNodes
  rw [hfun]

/-- The literal source expression Int(S') ∪ {t₀} for the fixed
old part of the signature reconstructed by Lemma 27. -/
noncomputable def oldSignatureBase
    {b n l : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    List (Node b) :=
  SkewTree.interior (StarredSignature.signatureTree O cut hout) ++ [cut]

/-- The precise printed tree component S_w of Lemma 27's map Q,
with actual literal R-derived D₂ coordinates and safe cone maps. -/
noncomputable def sourceSignatureNodes
    {b n l k m : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel)) :
    Finset (Node b) :=
  signatureNodes T hcomplete cut hcutT hlevel hm
    (oldSignatureBase O cut hout) x

/-- For the source's literal signature and marker indexing, the
tree part of Q is invariant under the all-Gamma₂ smoothness case. -/
theorem sourceSignatureNodes_eq_of_gamma2_smooth
    {b n l k m : Nat} {α : Type*}
    (O : StarredSignature.StarredWord b n l α
      (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    (hout : ∀ t, t ∈ StarredSignature.exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (hST : ∀ t, t ∈ O.tree → t ∈ T)
    (hcutT : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (x y : MixedProduct.Element b (k - (m + 1))
      (LiteralFrontierCount.frontiers T cut).length α
      (LiteralMarkerProductKind.kind
        O cut hcut hmax hout T hcomplete hST hcutT hlevel))
    (hxy : MixedProduct.SmoothRelated (fun _ => false) x y) :
    sourceSignatureNodes O cut hcut hmax hout T hcomplete hST hcutT
        hlevel hm x =
      sourceSignatureNodes O cut hcut hmax hout T hcomplete hST hcutT
        hlevel hm y :=
  signatureNodes_eq_of_gamma2_smooth T hcomplete cut hcutT
    hlevel hm (oldSignatureBase O cut hout) x y hxy

end DualTree.Lemma27SignatureTree
