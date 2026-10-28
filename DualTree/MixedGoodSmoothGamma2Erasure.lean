import DualTree.MixedGood
import DualTree.SmoothRelation

/-!
# Erase one Γ₂ bullet letter from a c-good smooth colouring

A c-good colouring can remember the observed letter at each D₂
marker. For a Γ₂ coordinate, Definition 21 smoothness lets us change
that letter while holding the marked point and all letters outside
its inclusive successor cone fixed.

The selected variable occurs only above its own root. Re-evaluating
that one variable therefore changes no exterior letter and stays
inside the actual mixed-word span. Together with c-goodness this
proves that the chosen Γ₂ letter is irrelevant when other bullet
record entries agree. This does not claim whole-span monochromaticity.
-/

namespace DualTree.MixedProduct

/-- Modify just one genuine local variable assignment at a D₂
marked root, keeping all other coordinates and markers fixed. -/
noncomputable def reassignMarkedLetter
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (i : BulletIndex kind)
    (a : β) : Element b n d β kind := by
  classical
  exact {
    words := fun j =>
      if _ : j = i.1 then
        SpanAudit.eval (f.vector.components j).word
          (fun v =>
            if v.1 = x.bulletPoint i then a
            else (Classical.choose (hx.1 j)) v)
      else x.words j
    upPoint := x.upPoint
    bulletPoint := x.bulletPoint
  }

/-- The one-variable reassignment remains in the true f span. -/
theorem reassignMarkedLetter_mem_span
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (i : BulletIndex kind)
    (a : β) :
    reassignMarkedLetter f x hx i a ∈ f.span := by
  classical
  refine ⟨?_, hx.2.1, hx.2.2⟩
  intro j
  by_cases hji : j = i.1
  · subst j
    refine ⟨(fun v => if v.1 = x.bulletPoint i
      then a else (Classical.choose (hx.1 i.1)) v), ?_⟩
    simp [reassignMarkedLetter]
  · simpa [reassignMarkedLetter, hji] using hx.1 j

theorem reassignMarkedLetter_bulletPoint
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (i j : BulletIndex kind)
    (a : β) :
    (reassignMarkedLetter f x hx i a).bulletPoint j = x.bulletPoint j :=
  rfl

/-- The actual letter at the marked root is the chosen new value. -/
theorem reassignMarkedLetter_at_mark
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (i : BulletIndex kind)
    (a : β) :
    (reassignMarkedLetter f x hx i a).words i.1 (x.bulletPoint i) = a := by
  classical
  let v : (f.vector.components i.1).Vars :=
    ⟨x.bulletPoint i, hx.2.2 i⟩
  have hroot :
      (f.vector.components i.1).word (x.bulletPoint i) =
        Sum.inr v :=
    (f.vector.components i.1).toVariableWord.atRoot v
  simp [reassignMarkedLetter, SpanAudit.eval,
    SpanAudit.evalSymbol, hroot, v]

/-- The entire word in any other coordinate is unchanged. -/
theorem reassignMarkedLetter_other_words
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (i : BulletIndex kind)
    (a : β)
    (j : Fin d)
    (hji : j ≠ i.1) :
    (reassignMarkedLetter f x hx i a).words j = x.words j := by
  classical
  simp [reassignMarkedLetter, hji]

/-- The modified component word agrees with the original outside
the inclusive successor cone, using the genuine variable below-root
axiom and the existing component evaluation witness. -/
theorem reassignMarkedLetter_outside_cone
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (i : BulletIndex kind)
    (a : β)
    (s : BoundedNode b n)
    (hout : ¬ IsPrefix (x.bulletPoint i).1 s.1) :
    (reassignMarkedLetter f x hx i a).words i.1 s =
      x.words i.1 s := by
  classical
  let σ := Classical.choose (hx.1 i.1)
  have hxσ : SpanAudit.eval
      (f.vector.components i.1).word σ = x.words i.1 :=
    Classical.choose_spec (hx.1 i.1)
  calc
    (reassignMarkedLetter f x hx i a).words i.1 s =
      SpanAudit.eval (f.vector.components i.1).word
        (fun v => if v.1 = x.bulletPoint i then a else σ v) s := by
          simp [reassignMarkedLetter, σ]
    _ = SpanAudit.eval (f.vector.components i.1).word σ s := by
      cases hw : (f.vector.components i.1).word s with
      | inl letter =>
          simp [SpanAudit.eval, SpanAudit.evalSymbol, hw]
      | inr v =>
          have hvne : v.1 ≠ x.bulletPoint i := by
            intro hroot
            have hpre := (f.vector.components i.1).toVariableWord.below
              v s hw
            apply hout
            simpa [hroot] using hpre
          simp [SpanAudit.eval, SpanAudit.evalSymbol, hw, hvne]
    _ = x.words i.1 s := congrFun hxσ s

/-- Reassigning one marked variable at a Γ₂ coordinate is a
genuine smooth-related change in the actual mixed-word span. -/
theorem reassignMarkedLetter_smooth_gamma2
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (gamma1 : BulletIndex kind → Bool)
    (i : BulletIndex kind)
    (hgamma : gamma1 i = false)
    (a : β) :
    SmoothRelated gamma1 x (reassignMarkedLetter f x hx i a) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hji : j ≠ i.1 := by
      intro h
      subst j
      exact hj i.2
    exact (reassignMarkedLetter_other_words
      f x hx i a j hji).symm
  · intro j
    rfl
  · intro j
    by_cases heq : j = i
    · subst j
      simp only [hgamma]
      refine ⟨rfl, ?_⟩
      intro t ht
      exact (reassignMarkedLetter_outside_cone
        f x hx i a t ht).symm
    · have hji : j.1 ≠ i.1 := by
        intro h
        exact heq (Subtype.ext h)
      have hw : x.words j.1 =
          (reassignMarkedLetter f x hx i a).words j.1 :=
        (reassignMarkedLetter_other_words f x hx i a j.1 hji).symm
      cases hg : gamma1 j with
      | true =>
          simpa [hg] using hw
      | false =>
          change x.bulletPoint j =
            (reassignMarkedLetter f x hx i a).bulletPoint j ∧
            ∀ t : BoundedNode b n,
              ¬ IsPrefix (x.bulletPoint j).1 t.1 →
              x.words j.1 t =
                (reassignMarkedLetter f x hx i a).words j.1 t
          exact ⟨rfl, fun t _ => congrFun hw t⟩

/-- Combined c-good and smooth Γ₂ conclusion. If two span points
agree on all marked positions and on every OTHER observed bullet
letter, then their colours agree, even if this Γ₂ letter differs.
No full-starred-span monochromaticity is inferred. -/
theorem good_smooth_erase_one_gamma2_letter
    {b n d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k β aux kind)
    (c : Element b n d β kind → γ)
    (gamma1 : BulletIndex kind → Bool)
    (hgood : Good c f)
    (hsmooth : ∀ x y, SmoothRelated gamma1 x y → c x = c y)
    (i : BulletIndex kind)
    (hgamma : gamma1 i = false)
    (x y : Element b n d β kind)
    (hx : x ∈ f.span) (hy : y ∈ f.span)
    (hpoints : ∀ j : BulletIndex kind,
      x.bulletPoint j = y.bulletPoint j)
    (hletters : ∀ j : BulletIndex kind, j ≠ i →
      x.words j.1 (x.bulletPoint j) =
        y.words j.1 (y.bulletPoint j)) :
    c x = c y := by
  classical
  let z := reassignMarkedLetter f x hx i
    (y.words i.1 (y.bulletPoint i))
  have hz : z ∈ f.span :=
    reassignMarkedLetter_mem_span f x hx i _
  have hxz : SmoothRelated gamma1 x z :=
    reassignMarkedLetter_smooth_gamma2
      f x hx gamma1 i hgamma _
  have hpts : ∀ j : BulletIndex kind,
      z.bulletPoint j = y.bulletPoint j := by
    intro j
    exact (reassignMarkedLetter_bulletPoint f x hx i j _).trans
      (hpoints j)
  have hvals : ∀ j : BulletIndex kind,
      z.words j.1 (z.bulletPoint j) =
        y.words j.1 (y.bulletPoint j) := by
    intro j
    by_cases hji : j = i
    · subst j
      change (reassignMarkedLetter f x hx i
        (y.words i.1 (y.bulletPoint i))).words i.1
          (x.bulletPoint i) =
        y.words i.1 (y.bulletPoint i)
      exact reassignMarkedLetter_at_mark
        f x hx i (y.words i.1 (y.bulletPoint i))
    · have hcoord : j.1 ≠ i.1 := by
        intro h
        exact hji (Subtype.ext h)
      change (reassignMarkedLetter f x hx i
          (y.words i.1 (y.bulletPoint i))).words j.1
            (x.bulletPoint j) =
        y.words j.1 (y.bulletPoint j)
      rw [reassignMarkedLetter_other_words
        f x hx i (y.words i.1 (y.bulletPoint i)) j.1 hcoord]
      exact hletters j hji
  exact (hsmooth x z hxz).trans (hgood hz hy hpts hvals)

end DualTree.MixedProduct
