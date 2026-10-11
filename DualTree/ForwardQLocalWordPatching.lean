import DualTree.ForwardQDisjointWordCones
import DualTree.ForwardQActualStarredSpace

/-!
# Patching decoded words in disjoint corrected-Q marked cones

The actual corrected Q construction has a finite family of selected
projected D₂ points. Its inclusive cones are pairwise disjoint in
the *whole* homogeneous tree, and no old source variable root lies
in any selected cone (ForwardQDisjointWordCones).

For any family of translated local symbol maps
  local : D₂ → b^{<n} → α ⊔ Vars(source),
define the global symbol map by taking local i inside the
selected projected cone i, and the old source word outside
all such cones. Pairwise cone disjointness makes this
choice unambiguous.

The old source word's at-root axiom is automatically
preserved. If every locally decoded variable occurrence
also lies above its named *source* variable root, then
the patched global symbol map is an honest VariableWord
with exactly the original source variable roots. The
specific three-way cone decoder has not yet been shown
to satisfy the local occurrence-prefix premise; nor does
this file prove the colouring pullback or the recursive
height constraints of the printed Lemma 27.

The selector and proofs are noncomputable where needed;
all equalities are actual source-facing Lean statements.
-/

namespace DualTree.ForwardQLocalWordPatching

open ForwardSourceQTree

/-- At a fixed position of the homogeneous tree, choose the
unique selected D₂ projected cone containing that position,
if any. The geometric disjointness theorem ensures uniqueness. -/
noncomputable def selectedCone
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (t : BoundedNode b n) :
    Option (MixedProduct.BulletIndex (kind c)) := by
  classical
  exact if h : ∃ i : MixedProduct.BulletIndex (kind c),
      IsPrefix (markedProjection c x i).1 t.1 then
    some (Classical.choose h)
  else none

/-- No source variable-root coordinate is in any selected
marked cone, so the global selector returns none at roots. -/
theorem selectedCone_none_at_source_root
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (v : c.source.word.Vars) :
    selectedCone c x v.1 = none := by
  classical
  have hnone : ¬ ∃ i : MixedProduct.BulletIndex (kind c),
      IsPrefix (markedProjection c x i).1 v.1.1 := by
    rintro ⟨i, hi⟩
    exact (ForwardQDisjointWordCones.projected_cone_avoids_source_root
      c x i v) hi
  simp [selectedCone, hnone]

/-- An ambient coordinate above a selected projection is
assigned to precisely that projection's D₂ index, never
to a different cone. -/
theorem selectedCone_eq_some_of_prefix
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (i : MixedProduct.BulletIndex (kind c))
    (t : BoundedNode b n)
    (hi : IsPrefix (markedProjection c x i).1 t.1) :
    selectedCone c x t = some i := by
  classical
  have hExists : ∃ j : MixedProduct.BulletIndex (kind c),
      IsPrefix (markedProjection c x j).1 t.1 := ⟨i, hi⟩
  have hchosen : IsPrefix
      (markedProjection c x (Classical.choose hExists)).1 t.1 :=
    Classical.choose_spec hExists
  have heq : Classical.choose hExists = i := by
    by_contra hne
    exact (ForwardQDisjointWordCones.projected_cones_no_common_extension
      c x (Classical.choose hExists) i hne t.1) ⟨hchosen, hi⟩
  simp [selectedCone, hExists, heq]

/-- Outside every projected marked cone, the source word is
used without changing any original symbols. Inside the
unique selected cone we use the corresponding local map. -/
noncomputable def patchedSymbol
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (coneWord : MixedProduct.BulletIndex (kind c) →
      BoundedNode b n → Sum α c.source.word.Vars)
    (t : BoundedNode b n) :
    Sum α c.source.word.Vars :=
  match selectedCone c x t with
  | some i => coneWord i t
  | none => c.source.word.word t

/-- At any position in a selected cone, the patched word is
literally the local decoded symbol map for that cone. -/
theorem patchedSymbol_inside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (coneWord : MixedProduct.BulletIndex (kind c) →
      BoundedNode b n → Sum α c.source.word.Vars)
    (i : MixedProduct.BulletIndex (kind c))
    (t : BoundedNode b n)
    (hi : IsPrefix (markedProjection c x i).1 t.1) :
    patchedSymbol c x coneWord t = coneWord i t := by
  simp [patchedSymbol, selectedCone_eq_some_of_prefix c x i t hi]

/-- At any position outside *all* marked cones, the patched
word agrees exactly with the original source word. -/
theorem patchedSymbol_outside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (coneWord : MixedProduct.BulletIndex (kind c) →
      BoundedNode b n → Sum α c.source.word.Vars)
    (t : BoundedNode b n)
    (ht : ∀ i : MixedProduct.BulletIndex (kind c),
      ¬ IsPrefix (markedProjection c x i).1 t.1) :
    patchedSymbol c x coneWord t = c.source.word.word t := by
  classical
  have hnone : ¬ ∃ i : MixedProduct.BulletIndex (kind c),
      IsPrefix (markedProjection c x i).1 t.1 := by
    rintro ⟨i, hi⟩
    exact ht i hi
  simp [patchedSymbol, selectedCone, hnone]

/-- The global patched symbols retain the old at-root axiom
without imposing any special root behavior on local maps:
selected marked cones avoid all old variable roots. -/
theorem patchedSymbol_at_source_root
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (coneWord : MixedProduct.BulletIndex (kind c) →
      BoundedNode b n → Sum α c.source.word.Vars)
    (v : c.source.word.Vars) :
    patchedSymbol c x coneWord v.1 = Sum.inr v := by
  simp [patchedSymbol, selectedCone_none_at_source_root c x v,
    c.source.word.atRoot v]

/-- Root-aligned local variable symbols are the only extra
word-level hypothesis: if a translated local cone word
uses source variable v at ambient coordinate t, the
original source root of v must prefix that occurrence. -/
noncomputable def patchedVariableWord
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (coneWord : MixedProduct.BulletIndex (kind c) →
      BoundedNode b n → Sum α c.source.word.Vars)
    (haligned : ∀ (i : MixedProduct.BulletIndex (kind c))
      (v : c.source.word.Vars) (t : BoundedNode b n),
      coneWord i t = Sum.inr v → IsPrefix v.1.1 t.1) :
    DualTree.VariableWord b n α := {
  support := c.source.word.support
  support_nodup := c.source.word.support_nodup
  word := patchedSymbol c x coneWord
  atRoot := by
    intro v
    exact patchedSymbol_at_source_root c x coneWord v
  below := by
    intro v t h
    cases hsel : selectedCone c x t with
    | none =>
        have hsource : c.source.word.word t = Sum.inr v := by
          simpa [patchedSymbol, hsel] using h
        exact c.source.word.below v t hsource
    | some i =>
        have hlocal : coneWord i t = Sum.inr v := by
          simpa [patchedSymbol, hsel] using h
        exact haligned i v t hlocal
}

/-- The resulting variable word has *exactly* the source
root support, not merely a subset of it. -/
theorem patchedVariableWord_support
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (coneWord : MixedProduct.BulletIndex (kind c) →
      BoundedNode b n → Sum α c.source.word.Vars)
    (haligned : ∀ (i : MixedProduct.BulletIndex (kind c))
      (v : c.source.word.Vars) (t : BoundedNode b n),
      coneWord i t = Sum.inr v → IsPrefix v.1.1 t.1) :
    (patchedVariableWord c x coneWord haligned).support =
      c.source.word.support := rfl

/-- The patched word's symbol at each ambient position is
exactly the cone-wise reconstructed symbol map. -/
theorem patchedVariableWord_symbol
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (coneWord : MixedProduct.BulletIndex (kind c) →
      BoundedNode b n → Sum α c.source.word.Vars)
    (haligned : ∀ (i : MixedProduct.BulletIndex (kind c))
      (v : c.source.word.Vars) (t : BoundedNode b n),
      coneWord i t = Sum.inr v → IsPrefix v.1.1 t.1)
    (t : BoundedNode b n) :
    (patchedVariableWord c x coneWord haligned).word t =
      patchedSymbol c x coneWord t := rfl

end DualTree.ForwardQLocalWordPatching
