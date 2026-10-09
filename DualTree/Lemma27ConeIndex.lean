import DualTree.Lemma27SignatureTree
import DualTree.InverseConeTails

/-!
# Unique cone-coordinate addresses for Lemma 27

The printed definition of Q and the reconstructed word f' use clauses
indexed by i ∈ [d] and z in a local b-ary tree, satisfying
t = P_i(z). Before these clauses can be assembled into a global
function, the coordinate pair (i,z) must be unique.

On the corrected common tail domain, the actual canonical cone
projections are injective within each cone, and different minimal
frontiers have disjoint cones. We combine both results to give
a globally injective map from coordinate/tail pairs to support nodes.

A partial inverse returns the unique pair if a support node is in
this image, or none otherwise. This is the source-facing selector
needed to define Q's cases on whole source-variable fibres.
No global Q word or colouring is constructed here.
-/

namespace DualTree.Lemma27ConeIndex

/-- One frontier coordinate and one address in the certified
common local b-ary tree. -/
abbrev Slot {b k m : Nat}
    (T : List (Node b)) (cut : Node b) :=
  Fin (LiteralFrontierCount.frontiers T cut).length ×
    BoundedNode b (k - (m + 1))

/-- The support root addressed by a frontier coordinate and local tail. -/
noncomputable def projectSlot {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (s : Slot (k := k) (m := m) T cut) :
    {t : Node b // t ∈ T} :=
  UniformConeDomains.projectCommon T hcomplete cut hcut hlevel hm
    (Lemma27SignatureTree.frontierAt T cut s.1)
    (Lemma27SignatureTree.frontierAt_spec T cut s.1)
    s.2

/-- The projection lies above the frontier selected by the first coordinate. -/
theorem projectSlot_cone {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (s : Slot (k := k) (m := m) T cut) :
    IsPrefix (Lemma27SignatureTree.frontierAt T cut s.1).1
      (projectSlot T hcomplete cut hcut hlevel hm s).1 :=
  UniformConeDomains.projectCommon_cone T hcomplete cut hcut hlevel hm
    (Lemma27SignatureTree.frontierAt T cut s.1)
    (Lemma27SignatureTree.frontierAt_spec T cut s.1) s.2

/-- Two different global coordinate/tail pairs never address
the same support vertex. -/
theorem projectSlot_injective {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m) :
    Function.Injective
      (projectSlot T hcomplete cut hcut hlevel hm) := by
  intro s t heq
  rcases s with ⟨i, z⟩
  rcases t with ⟨j, w⟩
  have hi := Lemma27SignatureTree.frontierAt_spec T cut i
  have hj := Lemma27SignatureTree.frontierAt_spec T cut j
  have hpi : IsPrefix
      (Lemma27SignatureTree.frontierAt T cut i).1
      (projectSlot T hcomplete cut hcut hlevel hm (i, z)).1 :=
    projectSlot_cone T hcomplete cut hcut hlevel hm (i, z)
  have hpj : IsPrefix
      (Lemma27SignatureTree.frontierAt T cut j).1
      (projectSlot T hcomplete cut hcut hlevel hm (j, w)).1 :=
    projectSlot_cone T hcomplete cut hcut hlevel hm (j, w)
  have hpj' : IsPrefix
      (Lemma27SignatureTree.frontierAt T cut j).1
      (projectSlot T hcomplete cut hcut hlevel hm (i, z)).1 := by
    rw [heq]
    exact hpj
  have hfront :
      (Lemma27SignatureTree.frontierAt T cut i).1 =
      (Lemma27SignatureTree.frontierAt T cut j).1 :=
    CutFrontier.frontier_unique_above T (fun u => PaperAux u cut)
      hi hj hpi hpj'
  let F := LiteralFrontierCount.frontiers T cut
  have hget : F.get i = F.get j := by
    simpa [F, Lemma27SignatureTree.frontierAt] using hfront
  have hequiv :
      (List.Nodup.getEquiv F (LiteralFrontierCount.frontiers_nodup T cut)) i =
      (List.Nodup.getEquiv F (LiteralFrontierCount.frontiers_nodup T cut)) j :=
    Subtype.ext hget
  have hindex : i = j :=
    (List.Nodup.getEquiv F
      (LiteralFrontierCount.frontiers_nodup T cut)).injective hequiv
  subst j
  have hlocal :
      UniformConeDomains.projectCommon T hcomplete cut hcut hlevel hm
        (Lemma27SignatureTree.frontierAt T cut i)
        (Lemma27SignatureTree.frontierAt_spec T cut i) z =
      UniformConeDomains.projectCommon T hcomplete cut hcut hlevel hm
        (Lemma27SignatureTree.frontierAt T cut i)
        (Lemma27SignatureTree.frontierAt_spec T cut i) w := heq
  have hzw := InverseConeTails.projectCommon_injective
    T hcomplete cut hcut hlevel hm
    (Lemma27SignatureTree.frontierAt T cut i)
    (Lemma27SignatureTree.frontierAt_spec T cut i) hlocal
  simp [hzw]

/-- The unique coordinate/tail pair of a support vertex in the
image of the common cone projections; absent when not in that image. -/
noncomputable def locateSlot {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (t : {t : Node b // t ∈ T}) :
    Option (Slot (k := k) (m := m) T cut) := by
  classical
  exact if h : ∃ s : Slot (k := k) (m := m) T cut,
    projectSlot T hcomplete cut hcut hlevel hm s = t then
    some (Classical.choose h)
  else none

/-- Any coordinate pair returned by the selector really projects
to the requested support root. -/
theorem locateSlot_spec {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (t : {t : Node b // t ∈ T})
    (s : Slot (k := k) (m := m) T cut)
    (h : locateSlot T hcomplete cut hcut hlevel hm t = some s) :
    projectSlot T hcomplete cut hcut hlevel hm s = t := by
  classical
  unfold locateSlot at h
  split_ifs at h with hw
  · cases h
    exact Classical.choose_spec hw

/-- Applying the partial selector to the image of a slot
recovers that slot exactly, with no ambiguity. -/
theorem locateSlot_projectSlot {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (s : Slot (k := k) (m := m) T cut) :
    locateSlot T hcomplete cut hcut hlevel hm
      (projectSlot T hcomplete cut hcut hlevel hm s) = some s := by
  classical
  unfold locateSlot
  split_ifs with h
  · have hs :
        Classical.choose h = s :=
      (projectSlot_injective T hcomplete cut hcut hlevel hm)
        (Classical.choose_spec h)
    simp [hs]
  · exact False.elim (h ⟨s, rfl⟩)

/-- A missing coordinate means precisely that this source root
does not lie in any certified local cone image. -/
theorem locateSlot_none_iff {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (t : {t : Node b // t ∈ T}) :
    locateSlot T hcomplete cut hcut hlevel hm t = none ↔
      ¬ ∃ s : Slot (k := k) (m := m) T cut,
        projectSlot T hcomplete cut hcut hlevel hm s = t := by
  classical
  unfold locateSlot
  split_ifs with h <;> simp [h]

end DualTree.Lemma27ConeIndex
