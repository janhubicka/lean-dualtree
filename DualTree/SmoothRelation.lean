import DualTree.PartialColoring
import DualTree.MixedProduct

/-!
# Smoothness from Definition 21

Fix a partition of the D2 coordinates into Gamma1 and Gamma2.  The smoothness
comparison fixes entire words in D0,D1,Gamma1, fixes the top-level D1 points,
and at a Gamma2 coordinate fixes the marked root and word values outside
its inclusive successor cone.  The successor cone includes the root itself,
as defined in Section 3.1 of the paper.

The resulting relation is an equivalence relation.  Consequently the
classwise-extension lemma applies to partial colorings satisfying its
compatibility condition.  Establishing compatibility for the particular Q
constructed in Lemma 27 is still a separate proof obligation.
-/

namespace DualTree.MixedProduct

/-- The exact comparison in Definition 21 for a fixed Gamma1/Gamma2 split. -/
def SmoothRelated
    {b n d : Nat} {α : Type*}
    {kind : Fin d → CoordKind}
    (gamma1 : BulletIndex kind → Bool)
    (x y : Element b n d α kind) : Prop :=
  (∀ i : Fin d, kind i ≠ CoordKind.bullet → x.words i = y.words i) ∧
  (∀ i : UpIndex kind, x.upPoint i = y.upPoint i) ∧
  (∀ i : BulletIndex kind,
    if gamma1 i then
      x.words i.1 = y.words i.1
    else
      x.bulletPoint i = y.bulletPoint i ∧
      ∀ t : BoundedNode b n,
        ¬ IsPrefix (x.bulletPoint i).1 t.1 →
        x.words i.1 t = y.words i.1 t)

theorem smoothRelated_refl
    {b n d : Nat} {α : Type*}
    {kind : Fin d → CoordKind}
    (gamma1 : BulletIndex kind → Bool)
    (x : Element b n d α kind) :
    SmoothRelated gamma1 x x := by
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    rfl
  · intro i
    rfl
  · intro i
    cases hg : gamma1 i with
    | true => simp [hg]
    | false => simp [hg]

theorem smoothRelated_symm
    {b n d : Nat} {α : Type*}
    {kind : Fin d → CoordKind}
    (gamma1 : BulletIndex kind → Bool)
    {x y : Element b n d α kind}
    (hxy : SmoothRelated gamma1 x y) :
    SmoothRelated gamma1 y x := by
  rcases hxy with ⟨hplain, hup, hbullet⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact (hplain i hi).symm
  · intro i
    exact (hup i).symm
  · intro i
    cases hg : gamma1 i with
    | true =>
        have hw : x.words i.1 = y.words i.1 := by
          simpa [hg] using hbullet i
        simpa [hg] using hw.symm
    | false =>
        have hi :
            x.bulletPoint i = y.bulletPoint i ∧
            (∀ t : BoundedNode b n,
              ¬ IsPrefix (x.bulletPoint i).1 t.1 →
                x.words i.1 t = y.words i.1 t) := by
          simpa [hg] using hbullet i
        have hreverse :
            y.bulletPoint i = x.bulletPoint i ∧
            (∀ t : BoundedNode b n,
              ¬ IsPrefix (y.bulletPoint i).1 t.1 →
                y.words i.1 t = x.words i.1 t) := by
          refine ⟨hi.1.symm, ?_⟩
          intro t ht
          have ht' : ¬ IsPrefix (x.bulletPoint i).1 t.1 := by
            simpa [hi.1] using ht
          exact (hi.2 t ht').symm
        simpa [hg] using hreverse

theorem smoothRelated_trans
    {b n d : Nat} {α : Type*}
    {kind : Fin d → CoordKind}
    (gamma1 : BulletIndex kind → Bool)
    {x y z : Element b n d α kind}
    (hxy : SmoothRelated gamma1 x y)
    (hyz : SmoothRelated gamma1 y z) :
    SmoothRelated gamma1 x z := by
  rcases hxy with ⟨hplain1, hup1, hbullet1⟩
  rcases hyz with ⟨hplain2, hup2, hbullet2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact (hplain1 i hi).trans (hplain2 i hi)
  · intro i
    exact (hup1 i).trans (hup2 i)
  · intro i
    cases hg : gamma1 i with
    | true =>
        have h1 : x.words i.1 = y.words i.1 := by
          simpa [hg] using hbullet1 i
        have h2 : y.words i.1 = z.words i.1 := by
          simpa [hg] using hbullet2 i
        simpa [hg] using h1.trans h2
    | false =>
        have h1 :
            x.bulletPoint i = y.bulletPoint i ∧
            (∀ t : BoundedNode b n,
              ¬ IsPrefix (x.bulletPoint i).1 t.1 →
                x.words i.1 t = y.words i.1 t) := by
          simpa [hg] using hbullet1 i
        have h2 :
            y.bulletPoint i = z.bulletPoint i ∧
            (∀ t : BoundedNode b n,
              ¬ IsPrefix (y.bulletPoint i).1 t.1 →
                y.words i.1 t = z.words i.1 t) := by
          simpa [hg] using hbullet2 i
        have hresult :
            x.bulletPoint i = z.bulletPoint i ∧
            (∀ t : BoundedNode b n,
              ¬ IsPrefix (x.bulletPoint i).1 t.1 →
                x.words i.1 t = z.words i.1 t) := by
          refine ⟨h1.1.trans h2.1, ?_⟩
          intro t ht
          have ht' : ¬ IsPrefix (y.bulletPoint i).1 t.1 := by
            simpa [h1.1] using ht
          exact (h1.2 t ht).trans (h2.2 t ht')
        simpa [hg] using hresult

/-- The smoothness comparison is an equivalence relation. -/
def smoothSetoid
    {b n d : Nat} {α : Type*}
    {kind : Fin d → CoordKind}
    (gamma1 : BulletIndex kind → Bool) :
    Setoid (Element b n d α kind) where
  r := SmoothRelated gamma1
  iseqv := ⟨smoothRelated_refl gamma1,
    smoothRelated_symm gamma1, smoothRelated_trans gamma1⟩

/-- Classwise-compatible starred colorings extend to total smooth colorings. -/
theorem exists_smooth_extension
    {b n d : Nat} {α C : Type*}
    {kind : Fin d → CoordKind}
    (gamma1 : BulletIndex kind → Bool)
    (D : Set (Element b n d α kind))
    (c : {x // x ∈ D} → C)
    (fallback : C)
    (hcompat :
      ∀ (x y : Element b n d α kind)
        (hx : x ∈ D) (hy : y ∈ D),
        SmoothRelated gamma1 x y → c ⟨x, hx⟩ = c ⟨y, hy⟩) :
    ∃ ctotal : Element b n d α kind → C,
      (∀ x (hx : x ∈ D), ctotal x = c ⟨x, hx⟩) ∧
      (∀ x y, SmoothRelated gamma1 x y → ctotal x = ctotal y) := by
  exact PartialColoring.exists_equivalence_respecting_extension
    (smoothSetoid gamma1) D c fallback hcompat

end DualTree.MixedProduct
