import DualTree.MixedGoodSmoothReducedRecord

/-!
# The two-root resource missing from the printed Corollary 22

Definition 11 permits dependence on a marked letter.  Definition 21 removes
that dependence at a Γ₂ coordinate directly, but a Γ₁ coordinate requires
two distinct variable roots.  Move its marker to a second root, reassign the
first root's variable, and move the marker back.  The two marker moves preserve
the colour by smoothness; the reassignment preserves it by c-goodness.

All intermediate points below belong to the actual mixed-word span.  Applying
this operation simultaneously at the Γ₁ coordinates, and then using the
already verified Γ₂ erasure, shows that colours depend only on Γ₂ marked
points.  The actual records need not be constant.

The two-root resource is derived below from intrinsic dimension at least two.
This is a conditional repair interface.  It does not construct a Ramsey word
or establish the proposed MTHJ/CT quantitative threshold.  Those are separate
proof obligations.
-/

namespace DualTree.Corollary22TwoRootRepair

open MixedProduct

/-- Every Γ₁ component has two genuinely distinct variable roots. -/
def HasTwoGamma1Roots
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (gamma1 : BulletIndex kind → Bool) : Prop :=
  ∀ i : BulletIndex kind, gamma1 i = true →
    ∃ s t : BoundedNode b n,
      s ∈ (f.vector.components i.1).support ∧
      t ∈ (f.vector.components i.1).support ∧ s ≠ t

/-- A genuine complete variable support of dimension at least two
contains two distinct roots. -/
theorem complete_support_has_two_roots
    {b n k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    (f : KVariableWord b n k β aux)
    (hk : 2 ≤ k) :
    ∃ s t : BoundedNode b n, s ∈ f.support ∧ t ∈ f.support ∧ s ≠ t := by
  have hc := f.complete_support
  change SkewTree.completeB aux k (f.support.map Subtype.val) = true at hc
  cases hs : f.support with
  | nil =>
      rw [hs] at hc
      simp [SkewTree.completeB, SkewTree.skewB, SkewTree.rootedB] at hc
  | cons s rest =>
      cases rest with
      | nil =>
          rw [hs] at hc
          simp [SkewTree.completeB, SkewTree.skewB, SkewTree.immediateSuccs,
            SkewTree.immediateSuccB, SkewTree.strictPrefixB,
            SkewTree.heightAt, SkewTree.preds] at hc
          omega
      | cons t rest =>
          have hnd : (s :: t :: rest).Nodup := by
            rw [← hs]
            exact f.toVariableWord.support_nodup
          have hst : s ≠ t := by
            intro heq
            have hnot := (List.nodup_cons.mp hnd).1
            exact hnot (by simp [heq])
          exact ⟨s, t, by simp [hs], by simp [hs], hst⟩

/-- Intrinsic dimension at least two supplies the needed resource
simultaneously at every Γ₁ coordinate, irrespective of its type order. -/
theorem hasTwoGamma1Roots_of_two_le_dimension
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (gamma1 : BulletIndex kind → Bool)
    (hk : 2 ≤ k) :
    HasTwoGamma1Roots f gamma1 := by
  intro i _
  exact complete_support_has_two_roots (f.vector.components i.1) hk

/-- Move only Γ₁ markers.  Every word and every D₁ leaf is unchanged. -/
noncomputable def moveGamma1Markers
    {b n d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (x : Element b n d β kind)
    (gamma1 : BulletIndex kind → Bool)
    (other : BulletIndex kind → BoundedNode b n) :
    Element b n d β kind :=
  { words := x.words
    upPoint := x.upPoint
    bulletPoint := fun i => if gamma1 i then other i else x.bulletPoint i }

/-- Γ₁ marker movement is permitted by the literal smoothness relation. -/
theorem moveGamma1Markers_smooth
    {b n d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (x : Element b n d β kind)
    (gamma1 : BulletIndex kind → Bool)
    (other : BulletIndex kind → BoundedNode b n) :
    SmoothRelated gamma1 x (moveGamma1Markers x gamma1 other) := by
  refine ⟨fun _ _ => rfl, fun _ => rfl, ?_⟩
  intro i
  cases hg : gamma1 i with
  | true => simp [hg, moveGamma1Markers]
  | false => simp [hg, moveGamma1Markers]

/-- The moved markers stay in the actual support of their own components. -/
theorem moveGamma1Markers_mem_span
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (gamma1 : BulletIndex kind → Bool)
    (other : BulletIndex kind → BoundedNode b n)
    (hother : ∀ i, gamma1 i = true →
      other i ∈ (f.vector.components i.1).support) :
    moveGamma1Markers x gamma1 other ∈ f.span := by
  refine ⟨hx.1, hx.2.1, ?_⟩
  intro i
  cases hg : gamma1 i with
  | true => simpa [moveGamma1Markers, hg] using hother i hg
  | false => simpa [moveGamma1Markers, hg] using hx.2.2 i

/-- Reassigning the marked variable does not change the letter at a
different support root, even when the two roots are comparable. -/
theorem reassignMarkedLetter_at_other_root
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (i : BulletIndex kind)
    (a : β)
    (s : BoundedNode b n)
    (hs : s ∈ (f.vector.components i.1).support)
    (hne : s ≠ x.bulletPoint i) :
    (reassignMarkedLetter f x hx i a).words i.1 s = x.words i.1 s := by
  classical
  let v : (f.vector.components i.1).Vars := ⟨s, hs⟩
  have hroot : (f.vector.components i.1).word s = Sum.inr v :=
    (f.vector.components i.1).toVariableWord.atRoot v
  have hσ :
      SpanAudit.eval (f.vector.components i.1).word
        (Classical.choose (hx.1 i.1)) = x.words i.1 :=
    Classical.choose_spec (hx.1 i.1)
  calc
    (reassignMarkedLetter f x hx i a).words i.1 s =
        (Classical.choose (hx.1 i.1)) v := by
      simp [reassignMarkedLetter, SpanAudit.eval,
        SpanAudit.evalSymbol, hroot, v, hne]
    _ = x.words i.1 s := by
      simpa [SpanAudit.eval, SpanAudit.evalSymbol, hroot] using congrFun hσ s

/-- Normalize Γ₁ observed letters using the existing genuine-span
reassignment construction, with its Γ₂ mask complemented. -/
noncomputable def normalizeGamma1Letters
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (gamma1 : BulletIndex kind → Bool)
    (fallback : β) : Element b n d β kind :=
  normalizeGamma2Letters f x hx (fun i => !(gamma1 i)) fallback

/-- Every Γ₁ normalized point is still in the original span. -/
theorem normalizeGamma1Letters_mem_span
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (gamma1 : BulletIndex kind → Bool)
    (fallback : β) :
    normalizeGamma1Letters f x hx gamma1 fallback ∈ f.span :=
  normalizeGamma2Letters_mem_span f x hx (fun i => !(gamma1 i)) fallback

/-- With two roots at each Γ₁ coordinate, resetting all Γ₁ marked
letters preserves the colour.  No finiteness or Ramsey premise is used. -/
theorem color_eq_normalizeGamma1Letters
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (hgood : Good c f)
    (hsmooth : ∀ x y, SmoothRelated gamma1 x y → c x = c y)
    (htwo : HasTwoGamma1Roots f gamma1)
    (fallback : β)
    (x : Element b n d β kind)
    (hx : x ∈ f.span) :
    c x = c (normalizeGamma1Letters f x hx gamma1 fallback) := by
  classical
  have hchoice : ∀ i : BulletIndex kind,
      ∃ s : BoundedNode b n,
        s ∈ (f.vector.components i.1).support ∧
        (gamma1 i = true → s ≠ x.bulletPoint i) := by
    intro i
    by_cases hg : gamma1 i = true
    · rcases htwo i hg with ⟨s, t, hs, ht, hst⟩
      by_cases hseq : s = x.bulletPoint i
      · refine ⟨t, ht, fun _ hteq => hst ?_⟩
        exact hseq.trans hteq.symm
      · exact ⟨s, hs, fun _ => hseq⟩
    · exact ⟨x.bulletPoint i, hx.2.2 i, fun h => (hg h).elim⟩
  let other : BulletIndex kind → BoundedNode b n :=
    fun i => Classical.choose (hchoice i)
  have hother : ∀ i, other i ∈ (f.vector.components i.1).support :=
    fun i => (Classical.choose_spec (hchoice i)).1
  have hne : ∀ i, gamma1 i = true → other i ≠ x.bulletPoint i :=
    fun i => (Classical.choose_spec (hchoice i)).2
  let z := normalizeGamma1Letters f x hx gamma1 fallback
  have hz : z ∈ f.span :=
    normalizeGamma1Letters_mem_span f x hx gamma1 fallback
  let X := moveGamma1Markers x gamma1 other
  let Z := moveGamma1Markers z gamma1 other
  have hX : X ∈ f.span :=
    moveGamma1Markers_mem_span f x hx gamma1 other (fun i _ => hother i)
  have hZ : Z ∈ f.span :=
    moveGamma1Markers_mem_span f z hz gamma1 other (fun i _ => hother i)
  have hpoints : ∀ i : BulletIndex kind, X.bulletPoint i = Z.bulletPoint i := by
    intro i
    rfl
  have hletters : ∀ i : BulletIndex kind,
      X.words i.1 (X.bulletPoint i) = Z.words i.1 (Z.bulletPoint i) := by
    intro i
    cases hg : gamma1 i with
    | true =>
        have hr := reassignMarkedLetter_at_other_root
          f x hx i fallback (other i) (hother i) (hne i hg)
        simpa [X, Z, z, moveGamma1Markers, normalizeGamma1Letters,
          normalizeGamma2Letters, i.2, hg] using hr.symm
    | false =>
        simp [X, Z, z, moveGamma1Markers, normalizeGamma1Letters,
          normalizeGamma2Letters, i.2, hg]
  calc
    c x = c X := hsmooth x X (moveGamma1Markers_smooth x gamma1 other)
    _ = c Z := hgood hX hZ hpoints hletters
    _ = c z := (hsmooth z Z (moveGamma1Markers_smooth z gamma1 other)).symm

/-- Smoothness plus c-goodness and the two-root resource erase ALL
observed marked letters.  Equality of the D₂ point tuples suffices. -/
theorem good_smooth_color_eq_of_bullet_points
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (hgood : Good c f)
    (hsmooth : ∀ x y, SmoothRelated gamma1 x y → c x = c y)
    (htwo : HasTwoGamma1Roots f gamma1)
    (fallback : β)
    (x y : Element b n d β kind)
    (hx : x ∈ f.span) (hy : y ∈ f.span)
    (hpoints : ∀ i : BulletIndex kind, x.bulletPoint i = y.bulletPoint i) :
    c x = c y := by
  let X := normalizeGamma1Letters f x hx gamma1 fallback
  let Y := normalizeGamma1Letters f y hy gamma1 fallback
  have hX : X ∈ f.span :=
    normalizeGamma1Letters_mem_span f x hx gamma1 fallback
  have hY : Y ∈ f.span :=
    normalizeGamma1Letters_mem_span f y hy gamma1 fallback
  have hpts : ∀ i : BulletIndex kind, X.bulletPoint i = Y.bulletPoint i :=
    hpoints
  have hvals : ∀ i : BulletIndex kind, gamma1 i = true →
      X.words i.1 (X.bulletPoint i) = Y.words i.1 (Y.bulletPoint i) := by
    intro i hg
    have hleft := normalizeGamma2Letters_at_bullet
      f x hx (fun j => !(gamma1 j)) fallback i
    have hright := normalizeGamma2Letters_at_bullet
      f y hy (fun j => !(gamma1 j)) fallback i
    have hleft' : X.words i.1 (X.bulletPoint i) = fallback := by
      change (normalizeGamma2Letters f x hx
        (fun j => !(gamma1 j)) fallback).words i.1 (x.bulletPoint i) = fallback
      simpa [hg] using hleft
    have hright' : Y.words i.1 (Y.bulletPoint i) = fallback := by
      change (normalizeGamma2Letters f y hy
        (fun j => !(gamma1 j)) fallback).words i.1 (y.bulletPoint i) = fallback
      simpa [hg] using hright
    exact hleft'.trans hright'.symm
  calc
    c x = c X := color_eq_normalizeGamma1Letters
      f c gamma1 hgood hsmooth htwo fallback x hx
    _ = c Y := good_smooth_color_eq_of_reduced_bullet_record
      f c gamma1 hgood hsmooth fallback X Y hX hY hpts hvals
    _ = c y := (color_eq_normalizeGamma1Letters
      f c gamma1 hgood hsmooth htwo fallback y hy).symm

/-- Γ₁ points themselves can also move freely.  Hence the only data
still visible to the colour are the Γ₂ marked points. -/
theorem good_smooth_color_eq_of_gamma2_points
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (hgood : Good c f)
    (hsmooth : ∀ x y, SmoothRelated gamma1 x y → c x = c y)
    (htwo : HasTwoGamma1Roots f gamma1)
    (fallback : β)
    (x y : Element b n d β kind)
    (hx : x ∈ f.span) (hy : y ∈ f.span)
    (hpoints : ∀ i : BulletIndex kind, gamma1 i = false →
      x.bulletPoint i = y.bulletPoint i) :
    c x = c y := by
  let Y := moveGamma1Markers y gamma1 x.bulletPoint
  have hY : Y ∈ f.span := moveGamma1Markers_mem_span
    f y hy gamma1 x.bulletPoint (fun i _ => hx.2.2 i)
  have hpts : ∀ i : BulletIndex kind, x.bulletPoint i = Y.bulletPoint i := by
    intro i
    cases hg : gamma1 i with
    | true => simp [Y, moveGamma1Markers, hg]
    | false => simpa [Y, moveGamma1Markers, hg] using hpoints i hg
  exact (good_smooth_color_eq_of_bullet_points
    f c gamma1 hgood hsmooth htwo fallback x Y hx hY hpts).trans
      (hsmooth y Y (moveGamma1Markers_smooth y gamma1 x.bulletPoint)).symm

/-- In the all-Γ₁ case the two-root hypothesis suffices for full
mixed-span monochromaticity, conditional on the supplied Good word. -/
theorem good_smooth_monochromatic_all_gamma1
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (hgood : Good c f)
    (hsmooth : ∀ x y, SmoothRelated (fun _ => true) x y → c x = c y)
    (htwo : HasTwoGamma1Roots f (fun _ => true))
    (fallback : β)
    (x y : Element b n d β kind)
    (hx : x ∈ f.span) (hy : y ∈ f.span) :
    c x = c y := by
  apply good_smooth_color_eq_of_gamma2_points
    f c (fun _ => true) hgood hsmooth htwo fallback x y hx hy
  intro i hi
  cases hi

/-- The quantitative repair's actual algebraic input: every globally
smooth, c-good mixed word of intrinsic dimension at least two has
colours determined just by its Γ₂ marked-point tuple. -/
theorem good_smooth_color_eq_of_two_le_dimension
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (hk : 2 ≤ k)
    (hgood : Good c f)
    (hsmooth : ∀ x y, SmoothRelated gamma1 x y → c x = c y)
    (fallback : β)
    (x y : Element b n d β kind)
    (hx : x ∈ f.span) (hy : y ∈ f.span)
    (hpoints : ∀ i : BulletIndex kind, gamma1 i = false →
      x.bulletPoint i = y.bulletPoint i) :
    c x = c y :=
  good_smooth_color_eq_of_gamma2_points
    f c gamma1 hgood hsmooth
    (hasTwoGamma1Roots_of_two_le_dimension f gamma1 hk)
    fallback x y hx hy hpoints

end DualTree.Corollary22TwoRootRepair
