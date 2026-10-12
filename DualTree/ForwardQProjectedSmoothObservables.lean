import DualTree.ForwardQActualCoordinateWord
import DualTree.ForwardQMarkerSmoothPartition

/-!
# Exact observable Q-word criterion for the smooth mixed product

On the actual corrected W-star domain, an input x has a genuine
starred Q output whose letter at P_i(z) is x.words i z. For a
Definition 21 split Gamma1/Gamma2 the observable local positions are:
  * every z in a nonbullet (D0) coordinate;
  * every z in a Gamma1 bullet coordinate (whole word fixed);
  * only z OUTSIDE the marked local cone in a Gamma2 coordinate.

This module proves that Definition 21's SmoothRelated relation is
EQUIVALENT to equality of the actual decoded Q-output symbols at
every such observable projected position, together with equality of
Gamma2 marked points. The existing corrected frame has no D1 inputs.

Crucially the observable predicate uses the marked point of x,
which is automatically shared by y in Gamma2; at Gamma1 the
point may move, and no unsupported equality of entire Q trees is
asserted. This is an exact source-facing input/output criterion,
not yet smoothness of an arbitrary simple colouring on output
starred words. The latter needs the canonical A-to-R simplicity
transport and specific variable-word refinement.
-/

namespace DualTree.ForwardQProjectedSmoothObservables

open ForwardSourceQTree
open ForwardQActualCoordinateWord

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQActualCoordinateWord.Index c

/-- Positions whose actual local Q-coordinate letters Definition 21
requires to remain fixed under the selected Gamma1/Gamma2 split.
No condition is imposed on letters INSIDE a Gamma2 marked cone. -/
def ObservableLocal
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (x : Input c)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) : Prop :=
  kind c i ≠ MixedProduct.CoordKind.bullet ∨
    ∃ j : MixedProduct.BulletIndex (kind c),
      j.1 = i ∧
        (gamma1 j = true ∨
          ¬ IsPrefix (x.bulletPoint j).1 z.1)

/-- Nonbullet coordinates are fully observable. In the corrected
Q frame these are precisely the D0 frontier coordinates. -/
theorem observable_nonbullet
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (x : Input c)
    (i : Index c)
    (hi : kind c i ≠ MixedProduct.CoordKind.bullet)
    (z : BoundedNode b (k - (m + 1))) :
    ObservableLocal c gamma1 x i z :=
  Or.inl hi

/-- The entire local coordinate word is observable for a Gamma1
bullet, even when its marked point subsequently moves. -/
theorem observable_gamma1
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (x : Input c)
    (j : MixedProduct.BulletIndex (kind c))
    (hj : gamma1 j = true)
    (z : BoundedNode b (k - (m + 1))) :
    ObservableLocal c gamma1 x j.1 z :=
  Or.inr ⟨j, rfl, Or.inl hj⟩

/-- At a Gamma2 bullet, precisely positions outside its marked
cone are forced observable by the smoothness relation. -/
theorem observable_gamma2_outside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (x : Input c)
    (j : MixedProduct.BulletIndex (kind c))
    (z : BoundedNode b (k - (m + 1)))
    (hout : ¬ IsPrefix (x.bulletPoint j).1 z.1) :
    ObservableLocal c gamma1 x j.1 z :=
  Or.inr ⟨j, rfl, Or.inr hout⟩

/-- Smooth-related actual inputs have identical original coordinate
letters at every observable local position. This is the exact
Definition 21 word part, with the D2 cases distinguished. -/
theorem local_letters_eq_of_smooth
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (x y : Input c)
    (hxy : MixedProduct.SmoothRelated gamma1 x y)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hobs : ObservableLocal c gamma1 x i z) :
    x.words i z = y.words i z := by
  rcases hobs with hplain | ⟨j, rfl, hcase⟩
  · exact congrFun (hxy.1 i hplain) z
  · cases hg : gamma1 j with
    | true =>
        have hwords : x.words j.1 = y.words j.1 := by
          simpa [hg] using hxy.2.2 j
        exact congrFun hwords z
    | false =>
        rcases hcase with htrue | hout
        · simp [hg] at htrue
        · have hpair :
              x.bulletPoint j = y.bulletPoint j ∧
                ∀ t : BoundedNode b (k - (m + 1)),
                  ¬ IsPrefix (x.bulletPoint j).1 t.1 →
                    x.words j.1 t = y.words j.1 t := by
            simpa [hg] using hxy.2.2 j
          exact hpair.2 z hout

/-- The ACTUAL corrected Q output symbol at every observable
projected local point agrees under a smooth mixed-product pair.
The projected address P_i(z) is identical for both inputs. -/
theorem Q_symbol_eq_on_observable
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : ForwardQActualStarredSpace.StarredInput c)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (hxy : MixedProduct.SmoothRelated gamma1 x.1 y.1)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (hobs : ObservableLocal c gamma1 x.1 i z) :
    ((coordinateConeData c x.1 fallback).onActualStarredQ
      hb c x hTbound).word.word (projectedBounded c hTbound i z) =
    ((coordinateConeData c y.1 fallback).onActualStarredQ
      hb c y hTbound).word.word (projectedBounded c hTbound i z) := by
  rw [coordinateConeData_Q_symbol_projected hb c x fallback hTbound i z,
      coordinateConeData_Q_symbol_projected hb c y fallback hTbound i z]
  exact congrArg
    (fun a : α => (Sum.inl a : Sum α c.source.word.Vars))
    (local_letters_eq_of_smooth c gamma1 x.1 y.1 hxy i z hobs)

/-- The only Q marked points that Definition 21 fixes are its
Gamma2 coordinates: Gamma1 marked points are permitted to move. -/
theorem gamma2_marked_Q_eq_of_smooth
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (x y : Input c)
    (hxy : MixedProduct.SmoothRelated gamma1 x y)
    (j : MixedProduct.BulletIndex (kind c))
    (hg : gamma1 j = false) :
    markedProjection c x j = markedProjection c y j := by
  have hpoint :
      x.bulletPoint j = y.bulletPoint j := by
    have hp :
        x.bulletPoint j = y.bulletPoint j ∧
          ∀ t : BoundedNode b (k - (m + 1)),
            ¬ IsPrefix (x.bulletPoint j).1 t.1 →
              x.words j.1 t = y.words j.1 t := by
      simpa [hg] using hxy.2.2 j
    exact hp.1
  simp only [markedProjection, hpoint]

/-- Equality of the ACTUAL canonical projected D2 node for a fixed
frontier index is equivalent to equality of its local marked tail.
The reverse implication follows from the checked T-inverse address
formula, not from any assumption that the Q tree has unique leaves. -/
theorem markedProjection_eq_iff_bulletPoint_eq
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x y : Input c)
    (j : MixedProduct.BulletIndex (kind c)) :
    markedProjection c x j = markedProjection c y j ↔
      x.bulletPoint j = y.bulletPoint j := by
  constructor
  · intro hp
    have hx :
        (ForwardCompleteBijection.inverseAddress
          c.T c.hcomplete c.hnon (markedProjection c x j)).1 =
          (ForwardCompleteBijection.inverseAddress
            c.T c.hcomplete c.hnon
            (ForwardOrderedProjections.frontierAt c.T c.cut j.1)).1 ++
              (x.bulletPoint j).1 :=
      ForwardUniformConeDomains.projectCommon_inverse
        c.T c.hcomplete c.hnon c.cut c.hcutT c.hm
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1)
        (ForwardOrderedProjections.frontierAt_spec c.T c.cut j.1)
        (x.bulletPoint j)
    have hy :
        (ForwardCompleteBijection.inverseAddress
          c.T c.hcomplete c.hnon (markedProjection c y j)).1 =
          (ForwardCompleteBijection.inverseAddress
            c.T c.hcomplete c.hnon
            (ForwardOrderedProjections.frontierAt c.T c.cut j.1)).1 ++
              (y.bulletPoint j).1 :=
      ForwardUniformConeDomains.projectCommon_inverse
        c.T c.hcomplete c.hnon c.cut c.hcutT c.hm
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1)
        (ForwardOrderedProjections.frontierAt_spec c.T c.cut j.1)
        (y.bulletPoint j)
    let base : Node b :=
      (ForwardCompleteBijection.inverseAddress
        c.T c.hcomplete c.hnon
        (ForwardOrderedProjections.frontierAt c.T c.cut j.1)).1
    have happend :
        base ++ (x.bulletPoint j).1 =
          base ++ (y.bulletPoint j).1 := by
      calc
        base ++ (x.bulletPoint j).1 =
            (ForwardCompleteBijection.inverseAddress
              c.T c.hcomplete c.hnon (markedProjection c x j)).1 :=
          hx.symm
        _ = (ForwardCompleteBijection.inverseAddress
              c.T c.hcomplete c.hnon (markedProjection c y j)).1 := by
          rw [hp]
        _ = base ++ (y.bulletPoint j).1 := hy
    have htail := congrArg (fun z : Node b => z.drop base.length) happend
    have hnode : (x.bulletPoint j).1 = (y.bulletPoint j).1 := by
      simpa [base] using htail
    exact Subtype.ext hnode
  · intro hp
    simp only [markedProjection, hp]

/-- Equality of actual decoded Q-output symbols at the
canonical P_i(z) is equivalent to equality of the REAL coordinate
letters x_i(z), independently of the Gamma split. In particular
we may store their observable fingerprint without an arbitrary
universe choice for the empty raw cone-variable type. -/
theorem Q_projected_symbol_eq_iff_local_word_eq
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : ForwardQActualStarredSpace.StarredInput c)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    (((coordinateConeData c x.1 fallback).onActualStarredQ
      hb c x hTbound).word.word (projectedBounded c hTbound i z) =
     ((coordinateConeData c y.1 fallback).onActualStarredQ
      hb c y hTbound).word.word (projectedBounded c hTbound i z)) ↔
      x.1.words i z = y.1.words i z := by
  rw [coordinateConeData_Q_symbol_projected hb c x fallback hTbound i z,
      coordinateConeData_Q_symbol_projected hb c y fallback hTbound i z]
  simp only [Sum.inl.injEq]

/-- Exact Q-observable fingerprint stored as ORIGINAL coordinate
letters, which the preceding theorem identifies pointwise with
the actual Q output symbols at every canonical projection.
Together with Gamma2 projected marker points this is precisely
the information visible in Definition 21. -/
def QObservableAgreement
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : ForwardQActualStarredSpace.StarredInput c)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t) : Prop :=
  (∀ (i : Index c) (z : BoundedNode b (k - (m + 1))),
    ObservableLocal c gamma1 x.1 i z →
      x.1.words i z = y.1.words i z) ∧
  (∀ j : MixedProduct.BulletIndex (kind c),
    gamma1 j = false →
      markedProjection c x.1 j = markedProjection c y.1 j)

/-- Every smooth-related corrected-starred input pair has identical
Q observables, with NO claim that their entire Q trees agree. -/
theorem Q_observables_of_smooth
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : ForwardQActualStarredSpace.StarredInput c)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (hxy : MixedProduct.SmoothRelated gamma1 x.1 y.1) :
    QObservableAgreement hb c x y gamma1 fallback hTbound := by
  constructor
  · intro i z hobs
    exact local_letters_eq_of_smooth c gamma1 x.1 y.1 hxy i z hobs
  · intro j hg
    exact gamma2_marked_Q_eq_of_smooth c gamma1 x.1 y.1 hxy j hg

/-- Conversely the Q-observable equalities recover ALL of
Definition 21: D0 full words, Gamma1 full words, Gamma2
points and outside-cone letters. There are no D1 coordinates
in the literal corrected Q frame. -/
theorem smooth_of_Q_observables
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : ForwardQActualStarredSpace.StarredInput c)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (hobs : QObservableAgreement hb c x y gamma1 fallback hTbound) :
    MixedProduct.SmoothRelated gamma1 x.1 y.1 := by
  have hlocal :
      ∀ (i : Index c) (z : BoundedNode b (k - (m + 1))),
        ObservableLocal c gamma1 x.1 i z →
          x.1.words i z = y.1.words i z := by
    intro i z hz
    exact hobs.1 i z hz
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    funext z
    exact hlocal i z (observable_nonbullet c gamma1 x.1 i hi z)
  · intro i
    have hno :
        kind c i.1 ≠ MixedProduct.CoordKind.up :=
      ForwardSortedMixedProduct.kind_ne_up
        c.source c.cut c.hcut c.hmax c.hout
        c.T c.hcomplete c.hnon c.hST c.hcutT c.hearly i.1
    exact False.elim (hno i.2)
  · intro j
    cases hg : gamma1 j with
    | true =>
        have hword : x.1.words j.1 = y.1.words j.1 := by
          funext z
          exact hlocal j.1 z
            (observable_gamma1 c gamma1 x.1 j hg z)
        simpa [hg] using hword
    | false =>
        have hproj : markedProjection c x.1 j =
            markedProjection c y.1 j := hobs.2 j hg
        have hpoint :
            x.1.bulletPoint j = y.1.bulletPoint j := by
          -- The selected canonical frontier projection is injective
          -- on local marked points.
          exact
            (markedProjection_eq_iff_bulletPoint_eq c x.1 y.1 j).mp hproj
        have houtside :
            ∀ z : BoundedNode b (k - (m + 1)),
              ¬ IsPrefix (x.1.bulletPoint j).1 z.1 →
                x.1.words j.1 z = y.1.words j.1 z := by
          intro z hz
          exact hlocal j.1 z
            (observable_gamma2_outside c gamma1 x.1 j z hz)
        simpa [hg] using And.intro hpoint houtside

/-- The mixed smooth relation on genuine corrected-starred inputs
is EXACTLY equality of the observable letters and Gamma2 markers
of their decoded original-letter Q outputs (via the checked
projection/letter equivalence above). This is the
input-output bridge needed before testing the specific simple
colouring in Lemma 27. -/
theorem smooth_iff_Q_observables
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : ForwardQActualStarredSpace.StarredInput c)
    (gamma1 : MixedProduct.BulletIndex (kind c) → Bool)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t) :
    MixedProduct.SmoothRelated gamma1 x.1 y.1 ↔
      QObservableAgreement hb c x y gamma1 fallback hTbound :=
  ⟨Q_observables_of_smooth hb c x y gamma1 fallback hTbound,
    smooth_of_Q_observables hb c x y gamma1 fallback hTbound⟩

end DualTree.ForwardQProjectedSmoothObservables
