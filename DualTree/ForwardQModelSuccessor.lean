import DualTree.ForwardQModelDirectionalIso
import DualTree.CanonicalSupportWalk

/-!
# Local successor transport for the actual corrected Q support

The checked model/Q prefix and outgoing-direction isomorphisms
should identify not merely cones but the canonical next step.
For each first-l homogeneous interior model address p and i<b,
the literal model child p++[i] belongs to the model interior or
its external boundary. Its concrete Q-realization is therefore
a support vertex, regardless of whether the moving terminal
is a genuine ambient immediate child (usually it is not).

We prove it is the immediate successor INSIDE THE FINITE Q SUPPORT
and is precisely the point selected by CanonicalSupportWalk.next.
This requires excluding intervening support vertices and
competing immediate successors in the same outgoing direction.

All statements concern ACTUAL corrected Q supports; none asserts
that arbitrary starred refinements realize the published reverse
auxiliary order or discharges the remaining Hall/Ramsey obligations.
-/

namespace DualTree.ForwardQModelSuccessor

open ForwardSourceQTree
open ForwardQModelVertexEquiv
open ForwardQModelPrefixIso
open ForwardQModelDirectionalIso
open ForwardModelBoundaryHeap

/-- Every immediate child of a first-l homogeneous interior address
is EITHER another interior node OR an external boundary node. -/
noncomputable def modelChild
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (p : ModelInteriorVertex c)
    (i : Fin b) : ModelShape c := by
  classical
  by_cases hinside : ModelInterior l (p.1 ++ [i])
  · exact Sum.inl ⟨p.1 ++ [i], hinside⟩
  · exact Sum.inr
      ⟨p.1 ++ [i], ⟨hinside, p.1, i, p.2, rfl⟩⟩

theorem modelChild_address
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (p : ModelInteriorVertex c)
    (i : Fin b) :
    modelAddress (modelChild c p i) = p.1 ++ [i] := by
  classical
  by_cases hinside : ModelInterior l (p.1 ++ [i])
  · simp [modelChild, hinside, modelAddress]
  · simp [modelChild, hinside, modelAddress]

/-- The literal child model cone exactly equals the prefix cone
of the ACTUAL Q vertex representing that child. -/
theorem modelQ_child_prefix_iff
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (p : ModelInteriorVertex c)
    (i : Fin b) (v : ModelShape c) :
    IsPrefix
      ((modelQVertexEquiv hb c x) (modelChild c p i)).1
      ((modelQVertexEquiv hb c x) v).1 ↔
    IsPrefix (p.1 ++ [i]) (modelAddress v) := by
  simpa only [modelChild_address] using
    (ForwardQModelPrefixIso.modelQ_prefix_iff_modelAddress
      hb c x (modelChild c p i) v)

/-- Unlike ordinary ambient words, Q-support edges may be stretched.
Nevertheless the actual model child lies in the correct outgoing
ambient direction cone from the actual model parent. -/
theorem modelQ_child_first_direction
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (p : ModelInteriorVertex c)
    (i : Fin b) :
    IsPrefix
      (((modelQVertexEquiv hb c x) (Sum.inl p)).1 ++ [i])
      ((modelQVertexEquiv hb c x) (modelChild c p i)).1 := by
  apply (modelQ_childCone_iff_modelAddress
    hb c x p (modelChild c p i) i).mp
  rw [modelChild_address]
  exact isPrefix_refl _

/-- Model parent and model child are strict support prefixes, even
when the ambient distance between them is greater than one. -/
theorem modelQ_parent_strict_child
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (p : ModelInteriorVertex c)
    (i : Fin b) :
    IsStrictPrefix
      ((modelQVertexEquiv hb c x) (Sum.inl p)).1
      ((modelQVertexEquiv hb c x) (modelChild c p i)).1 := by
  let s := ((modelQVertexEquiv hb c x) (Sum.inl p)).1
  let t := ((modelQVertexEquiv hb c x) (modelChild c p i)).1
  have hcone : IsPrefix (s ++ [i]) t :=
    modelQ_child_first_direction hb c x p i
  have hpre : IsPrefix s t :=
    isPrefix_trans ⟨[i], rfl⟩ hcone
  have hlen : s.length + 1 ≤ t.length := by
    simpa using (prefix_length_le hcone)
  have hne : s ≠ t := by
    intro heq
    rw [← heq] at hlen
    omega
  exact ⟨hpre, hne⟩

/-- There is NO Q-support vertex strictly between the model
parent and its selected model child. The proof uses the full
model/Q prefix reflection and the impossibility of an
intermediate finite word between p and p++[i]. -/
theorem modelQ_child_immediate
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (p : ModelInteriorVertex c)
    (i : Fin b) :
    SkewTree.immediateSuccB (nodes c x).toList
      ((modelQVertexEquiv hb c x) (Sum.inl p)).1
      ((modelQVertexEquiv hb c x) (modelChild c p i)).1 = true := by
  let e := modelQVertexEquiv hb c x
  let s := (e (Sum.inl p)).1
  let t := (e (modelChild c p i)).1
  have ht : t ∈ (nodes c x).toList := (e (modelChild c p i)).2
  have hst : IsStrictPrefix s t :=
    modelQ_parent_strict_child hb c x p i
  apply (SkewBranchGeometry.immediateSuccB_iff
    (nodes c x).toList s t).2
  refine ⟨ht, hst, ?_⟩
  intro u hu hbetween
  let v : ModelShape c := e.symm ⟨u, hu⟩
  have hv : (e v).1 = u := by
    dsimp [v]
    simp
  have hbefore : IsPrefix p.1 (modelAddress v) := by
    apply (ForwardQModelPrefixIso.modelQ_prefix_iff_modelAddress
      hb c x (Sum.inl p) v).mp
    change IsPrefix s (e v).1
    rw [hv]
    exact hbetween.1.1
  have hafter : IsPrefix (modelAddress v) (p.1 ++ [i]) := by
    have h := (ForwardQModelPrefixIso.modelQ_prefix_iff_modelAddress
      hb c x v (modelChild c p i)).mp
    have hq : IsPrefix (e v).1 t := by
      rw [hv]
      exact hbetween.2.1
    simpa only [modelChild_address] using h hq
  have hneqBefore : p.1 ≠ modelAddress v := by
    intro heq
    have hback : IsPrefix (e v).1 s := by
      apply (ForwardQModelPrefixIso.modelQ_prefix_iff_modelAddress
        hb c x v (Sum.inl p)).2
      change IsPrefix (modelAddress v) p.1
      rw [heq]
      exact isPrefix_refl _
    have hsame : s = u :=
      isPrefix_antisymm hbetween.1.1
        (by simpa only [hv] using hback)
    exact hbetween.1.2 hsame
  have hneqAfter : modelAddress v ≠ p.1 ++ [i] := by
    intro heq
    have hback : IsPrefix t (e v).1 := by
      apply (ForwardQModelPrefixIso.modelQ_prefix_iff_modelAddress
        hb c x (modelChild c p i) v).2
      rw [modelChild_address, heq]
      exact isPrefix_refl _
    have hsame : u = t :=
      isPrefix_antisymm hbetween.2.1
        (by simpa only [hv] using hback)
    exact hbetween.2.2 hsame
  have hlow : p.1.length < (modelAddress v).length :=
    MeetClosedFromBranching.length_lt_of_strictPrefix
      ⟨hbefore, hneqBefore⟩
  have hhigh : (modelAddress v).length < (p.1 ++ [i]).length :=
    MeetClosedFromBranching.length_lt_of_strictPrefix
      ⟨hafter, hneqAfter⟩
  simp only [List.length_append, List.length_singleton] at hhigh
  omega

/-- The literal canonical support-walk transition on the
actual Q support selects EXACTLY the realized model child.
No pre-assumed uniqueness of branches or fake ambient adjacency
is used: any competing immediate directional successor would
strictly contain this already immediate model child. -/
theorem modelQ_next_eq_modelChild
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (p : ModelInteriorVertex c)
    (i : Fin b) :
    CanonicalSupportWalk.next (nodes c x).toList
      ((modelQVertexEquiv hb c x) (Sum.inl p)).1 i =
    ((modelQVertexEquiv hb c x) (modelChild c p i)).1 := by
  let e := modelQVertexEquiv hb c x
  let s := (e (Sum.inl p)).1
  let t := (e (modelChild c p i)).1
  let T := (nodes c x).toList
  have ht : t ∈ T := (e (modelChild c p i)).2
  have hstrict : IsStrictPrefix s t :=
    modelQ_parent_strict_child hb c x p i
  have himm : SkewTree.immediateSuccB T s t = true :=
    modelQ_child_immediate hb c x p i
  have hcone : IsPrefix (s ++ [i]) t :=
    modelQ_child_first_direction hb c x p i
  have hfound : t ∈ SkewTree.branchWitnesses T s i :=
    (SkewBranchGeometry.mem_branchWitnesses_iff T s t i).2
      ⟨himm, hcone⟩
  have huniq : ∀ u, u ∈ SkewTree.branchWitnesses T s i → u = t := by
    intro u hu
    obtain ⟨huimm, hucone⟩ :=
      (SkewBranchGeometry.mem_branchWitnesses_iff T s u i).1 hu
    have humem : u ∈ T :=
      ((SkewBranchGeometry.immediateSuccB_iff T s u).1 huimm).1
    let v : ModelShape c := e.symm ⟨u, humem⟩
    have hv : (e v).1 = u := by
      dsimp [v]
      simp
    have hmodel : IsPrefix (p.1 ++ [i]) (modelAddress v) := by
      apply (modelQ_childCone_iff_modelAddress hb c x p v i).mpr
      change IsPrefix (s ++ [i]) (e v).1
      rw [hv]
      exact hucone
    have hprefix : IsPrefix t u := by
      have h := (ForwardQModelPrefixIso.modelQ_prefix_iff_modelAddress
        hb c x (modelChild c p i) v).2
      have hmodel' : IsPrefix (modelAddress (modelChild c p i))
          (modelAddress v) := by
        simpa only [modelChild_address] using hmodel
      simpa only [hv] using h hmodel'
    by_contra hne
    have hno :=
      ((SkewBranchGeometry.immediateSuccB_iff T s u).1 huimm).2.2
    exact hno t ht ⟨hstrict, ⟨hprefix, Ne.symm hne⟩⟩
  change CanonicalSupportWalk.next T s i = t
  cases hlist : SkewTree.branchWitnesses T s i with
  | nil =>
      have hn : t ∈ ([] : List (Node b)) := by
        simpa only [hlist] using hfound
      cases hn
  | cons z zs =>
      have hz : z ∈ SkewTree.branchWitnesses T s i := by
        simp [hlist]
      simpa [CanonicalSupportWalk.next, hlist] using (huniq z hz)

end DualTree.ForwardQModelSuccessor
