import DualTree.ForwardQFinalEnlargedInducedEvaluation
import DualTree.MixedGood

/-!
# The precise c-good versus starred-monochromatic gap

Definition 11's "c-good" property only canonizes the colouring
by the marked D₂ points and their observed letter values. It does
NOT in general say that the entire D₂-starred mixed span is
monochromatic. This is not an issue of the enlarged Q construction,
or of the relative order of its frontier coordinates.

For any genuine mixed variable word f, any D₂ index i, and any
point x in its span, assigning two different letters to the ONE
actual component variable at x.bulletPoint i produces two points
in the same span with all marked points unchanged but with
different values of the c-good observation at i.

Any admissibility condition depending ONLY on marked points is
preserved, including the corrected D₂ vector-one starred condition.
Consequently, as soon as an actual corrected starred point in
f.span exists and the alphabet has two letters, the observed D₂
letter colouring is c-good but is not monochromatic on the
entire corrected starred span.

This makes the logical gap between the source's mixed c-good
Ramsey theorem and a subsequent FULL monochromaticity claim
explicit and kernel checked. It does NOT by itself establish
smoothness of the observed-letter colouring for an arbitrary
Gamma1/Gamma2 partition: that separate qualification matters
when testing the printed Corollary 22.
The previously verified height-one smooth counterexample
remains in Corollary22Audit.
-/

namespace DualTree.MixedGoodStarredSpanObstruction

open MixedProduct
open ForwardSourceQTree
open ForwardQFinalRefinementRoots

/-- The actual colour-relevant data at one selected bullet marker:
the original marked point together with its observed LETTER.
For a fixed bullet index we retain just the letter here. -/
def colorAtBullet
    {b n d : Nat} {β : Type*}
    {kind : Fin d → CoordKind}
    (i : BulletIndex kind)
    (x : Element b n d β kind) : β :=
  x.words i.1 (x.bulletPoint i)

/-- This colour satisfies Definition 11's c-good condition on
EVERY genuine mixed-product variable word, because that
definition deliberately permits dependence on each marked
bullet-point letter. -/
theorem colorAtBullet_good
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (i : BulletIndex kind) :
    Good (colorAtBullet i) f := by
  intro x y hx hy hmarks hletters
  exact hletters i

/-- Re-evaluate precisely ONE component variable word with a
constant β-letter. All marked points, other components and D₁
up-markers are retained unchanged. This is an actual product
element, not a pointwise patch of the variable word itself. -/
noncomputable def recolorBullet
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (i : BulletIndex kind)
    (a : β) : Element b n d β kind := by
  classical
  exact {
    words := fun j =>
      if _ : j = i.1 then
        (f.vector.components j).toVariableWord.eval (fun _ => a)
      else x.words j
    upPoint := x.upPoint
    bulletPoint := x.bulletPoint
  }

/-- Recolouring one component by an ACTUAL constant variable
assignment keeps the entire mixed point in the genuine f span,
including all D₁/D₂ marked point membership conditions. -/
theorem recolorBullet_mem_span
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (i : BulletIndex kind)
    (a : β) :
    recolorBullet f x i a ∈ f.span := by
  classical
  refine ⟨?_, hx.2.1, hx.2.2⟩
  intro j
  by_cases hj : j = i.1
  · have hmem :
        (f.vector.components j).toVariableWord.eval
          (fun _ => a) ∈ (f.vector.components j).span :=
      ⟨fun _ => a, rfl⟩
    simpa [recolorBullet, hj] using hmem
  · simpa [recolorBullet, hj] using hx.1 j

/-- The marked point at the chosen coordinate is an actual
local variable root. Evaluating that component with a uniform
β-letter therefore forces the observed bullet-point letter
to be EXACTLY the chosen value. -/
theorem colorAtBullet_recolor
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (hx : x ∈ f.span)
    (i : BulletIndex kind)
    (a : β) :
    colorAtBullet i (recolorBullet f x i a) = a := by
  classical
  let v : (f.vector.components i.1).Vars :=
    ⟨x.bulletPoint i, hx.2.2 i⟩
  have hroot :
      (f.vector.components i.1).word (x.bulletPoint i) =
        Sum.inr v :=
    (f.vector.components i.1).toVariableWord.atRoot v
  simp [colorAtBullet, recolorBullet, VariableWord.eval,
    SpanAudit.eval, SpanAudit.evalSymbol, hroot]

/-- The newly evaluated ordinary coordinate words have NOT
changed a single D₂ marked point. -/
theorem recolorBullet_points
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : MixedProduct.VariableWord b n d k β aux kind)
    (x : Element b n d β kind)
    (i j : BulletIndex kind)
    (a : β) :
    (recolorBullet f x i a).bulletPoint j = x.bulletPoint j :=
  rfl

/-- The genuine corrected vector-one D₂ starred predicate
depends EXCLUSIVELY on marked points, so any re-evaluation
of ordinary words preserving those points remains starred. -/
theorem enlarged_starred_preserved_by_bullet_points
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (fallback : α)
    (x y : ForwardQEnlargedConstantWords.EnlargedInput c)
    (hx : ForwardQActualStarredSpace.IsStarred c
      (ForwardQEnlargedConstantWords.eraseAux c fallback x))
    (hpoints : ∀ i : BulletIndex (kind c),
      y.bulletPoint i = x.bulletPoint i) :
    ForwardQActualStarredSpace.IsStarred c
      (ForwardQEnlargedConstantWords.eraseAux c fallback y) := by
  have hordered :
      ForwardQIndexedTRanks.BulletLengthsOrdered c
        (ForwardQEnlargedConstantWords.eraseAux c fallback x) :=
    (ForwardQActualStarredSpace.isStarred_iff_bullet_lengths_ordered
      c _).1 hx
  apply (ForwardQActualStarredSpace.isStarred_iff_bullet_lengths_ordered
    c _).2
  intro i j hij
  have h := hordered i j hij
  change (x.bulletPoint i).1.length ≤
    (x.bulletPoint j).1.length at h
  change (y.bulletPoint i).1.length ≤
    (y.bulletPoint j).1.length
  simpa only [hpoints i, hpoints j] using h

/-- A correction of Definition 11 to full starred-span
monochromaticity is IMPOSSIBLE using c-goodness alone:
the observed-bullet-letter colouring is c-good for ANY f,
yet has two different colours in the corrected starred
part of f.span as soon as it has one genuine starred point
and its alphabet has two letters. -/
theorem colorAtBullet_not_monochromatic_starred_span
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (i : BulletIndex (kind g.core))
    (x : ForwardQEnlargedConstantWords.EnlargedStarredInput
      g.core fallback)
    (hx : x.1 ∈ f.span) :
    ¬ (∀ y z : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback,
      y.1 ∈ f.span → z.1 ∈ f.span →
      colorAtBullet i y.1 = colorAtBullet i z.1) := by
  intro hmono
  let a : Sum α (Fin (m + 1)) := Sum.inl fallback
  let b : Sum α (Fin (m + 1)) := Sum.inr ⟨0, Nat.zero_lt_succ m⟩
  let ya := recolorBullet f x.1 i a
  let yb := recolorBullet f x.1 i b
  have ha : ya ∈ f.span := recolorBullet_mem_span f x.1 hx i a
  have hb : yb ∈ f.span := recolorBullet_mem_span f x.1 hx i b
  have hsa : ForwardQActualStarredSpace.IsStarred g.core
      (ForwardQEnlargedConstantWords.eraseAux g.core fallback ya) :=
    enlarged_starred_preserved_by_bullet_points
      g.core fallback x.1 ya x.2
      (fun j => recolorBullet_points f x.1 i j a)
  have hsb : ForwardQActualStarredSpace.IsStarred g.core
      (ForwardQEnlargedConstantWords.eraseAux g.core fallback yb) :=
    enlarged_starred_preserved_by_bullet_points
      g.core fallback x.1 yb x.2
      (fun j => recolorBullet_points f x.1 i j b)
  have heq :=
    hmono ⟨ya, hsa⟩ ⟨yb, hsb⟩ ha hb
  have hcolA := colorAtBullet_recolor f x.1 hx i a
  have hcolB := colorAtBullet_recolor f x.1 hx i b
  change colorAtBullet i ya = colorAtBullet i yb at heq
  rw [hcolA, hcolB] at heq
  have hab : a ≠ b := by simp [a, b]
  exact hab heq

/-- In the source-facing corrected Lemma-27 frame, positive
local dimension q itself gives a genuine starred mixed-span
point, as previously verified. Thus the local bullet-observation
colouring separates two points in EVERY genuine enlarged
local mixed-word starred span whenever there is a D₂ coordinate.
The colouring is nevertheless c-good in Definition 11's sense.

No assertion that this colouring is smooth for all Gamma partitions
is made; see Corollary22Audit for an independently kernel-checked
smooth counterexample at the exact printed height-one bound. -/
theorem no_full_starred_monochromaticity_from_good
    {b n l k m q : Nat} {α : Type*}
    (g : ForwardQAmbientFibreFrame.FibreFrame b n l k m α)
    (f : LocalMixedWord g.core q (Sum α (Fin (m + 1))))
    (fallback : α)
    (hq : 0 < q)
    (i : BulletIndex (kind g.core)) :
    ¬ (∀ y z : ForwardQEnlargedConstantWords.EnlargedStarredInput
        g.core fallback,
      y.1 ∈ f.span → z.1 ∈ f.span →
      colorAtBullet i y.1 = colorAtBullet i z.1) := by
  let base :=
    ForwardQFinalEnlargedInducedEvaluation.enlargedInducedStarredInput
      g f fallback (fun _ => fallback) hq
  have hbase : base.1 ∈ f.span :=
    ForwardQFinalEnlargedInducedEvaluation.enlargedInducedStarredInput_mem_span
      g f fallback (fun _ => fallback) hq
  exact colorAtBullet_not_monochromatic_starred_span
    g f fallback i base hbase

end DualTree.MixedGoodStarredSpanObstruction
