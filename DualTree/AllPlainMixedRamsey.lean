import DualTree.VectorRayHalesJewett
import DualTree.GoodNoBullet

/-!
# A genuine finite mixed-product c-good Ramsey theorem in the D₀-only case

The previous positive result is a vector of honest 1-complete-skew
tree variable words. Here we transport it into the ACTUAL mixed-product
`VariableWord` and `Element` API used by Definition 11.

All d coordinates have kind `plain` (D₀). The up/leaf and bullet/marked
subtypes are then empty, so their data are filled by the elimination
principle, not by dummy or arbitrarily chosen points. The genuine mixed
span is exactly the vector word span.

Consequently the unconditional monochromatic vector Ramsey theorem
gives a genuine mixed-product variable word on whose span every
colouring is constant. By the verified NoBullet equivalence, this is
a real Definition-11 c-good existence theorem at intrinsic dimension 1.

This is the D₀-only case with D₁ = D₂ = ∅; it does NOT settle the
mixed theorem with marked D₂ points, D₁ leaves, or higher complete-skew
dimension. No false full starred-span statement is used.
-/

namespace DualTree.MixedProduct

/-- All coordinates are the ordinary word coordinates D₀. -/
def allPlainKind (d : Nat) : Fin d → CoordKind :=
  fun _ => CoordKind.plain

/-- The D₀-only kind has neither D₁ up indices nor D₂ bullet indices. -/
theorem allPlain_noBullet (d : Nat) :
    NoBullet (allPlainKind d) := by
  intro i hi
  cases hi

/-- Turn a vector of evaluated tree words into a genuine mixed-product
element. Both marked-coordinate functions have empty domains, not
fabricated support points. -/
def allPlainElement
    {b n d : Nat} {β : Type*}
    (words : Fin d → TreeWord b n β) :
    Element b n d β (allPlainKind d) where
  words := words
  upPoint := fun i => nomatch i.2
  bulletPoint := fun i => nomatch i.2

/-- There is no extra information in an all-D₀ mixed element:
its ordinary coordinate words determine the whole element. -/
theorem allPlainElement_words (x :
    Element b n d β (allPlainKind d)) :
    allPlainElement x.words = x := by
  cases x with
  | mk words up bullet =>
    have hup :
        up = (fun i : UpIndex (allPlainKind d) => nomatch i.2) := by
      funext i
      cases i.2
    have hbullet :
        bullet = (fun i : BulletIndex (allPlainKind d) => nomatch i.2) := by
      funext i
      cases i.2
    cases hup
    cases hbullet
    rfl

/-- Lift a genuine vector k-complete-skew tree word into the ACTUAL
mixed variable-word type with D₁ = D₂ = ∅. The condition on up-leaf
lists is discharged only because there are no D₁ coordinates. -/
def allPlainVariableWord
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    (v : VectorVariableWord b n d k β aux) :
    VariableWord b n d k β aux (allPlainKind d) where
  vector := v
  upLeaves := fun i => nomatch i.2
  upLeaves_nodup := fun i => nomatch i.2
  upLeaves_card := fun i => nomatch i.2
  up_support_skew := fun i => nomatch i.2

/-- Exact span correspondence, without an artificial singleton
up-leaf set or any dummy marked D₂ points. -/
theorem allPlainVariableWord_mem_span_iff
    {b n d k : Nat} {β : Type*}
    {aux : Node b → Node b → Bool}
    (v : VectorVariableWord b n d k β aux)
    (x : Element b n d β (allPlainKind d)) :
    x ∈ (allPlainVariableWord v).span ↔ x.words ∈ v.span := by
  constructor
  · intro hx
    exact hx.1
  · intro hw
    refine ⟨hw, ?_, ?_⟩
    · intro i
      cases i.2
    · intro i
      cases i.2

/-- An unconditional finite monochromatic mixed-product existence
theorem for all-D₀ kind and intrinsic complete-skew height ONE.
The support is a genuine vector 1-complete-skew tree family and
the conclusion quantifies over the entire evaluated MIXED span. -/
theorem exists_monochromatic_allPlain_height_one
    {b : Nat} (hb : 0 < b)
    (β γ : Type*) [Finite β] [Finite γ]
    (fallback : β) (d : Nat) :
    ∃ n : Nat,
      ∀ color : Element b n d β (allPlainKind d) → γ,
        ∃ f : VariableWord b n d 1 β
            (SkewTree.forwardAuxB (b := b)) (allPlainKind d),
          ∃ col : γ,
            ∀ x : Element b n d β (allPlainKind d),
              x ∈ f.span → color x = col := by
  obtain ⟨n, hn⟩ :=
    DualTree.VectorRayHalesJewett.exists_monochromatic_vector_one_root_tree_word
      hb β γ fallback d
  refine ⟨n, ?_⟩
  intro color
  let C : (Fin d → TreeWord b n β) → γ :=
    fun words => color (allPlainElement words)
  obtain ⟨v, col, hmono⟩ := hn C
  let f := allPlainVariableWord v
  refine ⟨f, col, ?_⟩
  intro x hx
  have hv : x.words ∈ v.span :=
    (allPlainVariableWord_mem_span_iff v x).mp hx
  calc
    color x = color (allPlainElement x.words) :=
      congrArg color (allPlainElement_words x).symm
    _ = C x.words := rfl
    _ = col := hmono x.words hv

/-- A positive and unconditional fragment of the ACTUAL
mixed-product Ramsey theorem (Definition 11), not merely a
vector-words monochromaticity theorem: when D₁ = D₂ = ∅
and k = 1, a sufficiently tall tree supplies a c-good
mixed-product word for EVERY finite colouring. -/
theorem exists_good_allPlain_height_one
    {b : Nat} (hb : 0 < b)
    (β γ : Type*) [Finite β] [Finite γ]
    (fallback : β) (d : Nat) :
    ∃ n : Nat,
      ∀ color : Element b n d β (allPlainKind d) → γ,
        ∃ f : VariableWord b n d 1 β
            (SkewTree.forwardAuxB (b := b)) (allPlainKind d),
          Good color f := by
  obtain ⟨n, hn⟩ :=
    exists_monochromatic_allPlain_height_one hb β γ fallback d
  refine ⟨n, ?_⟩
  intro color
  obtain ⟨f, col, hmono⟩ := hn color
  refine ⟨f, ?_⟩
  apply good_of_constant_on_span_of_noBullet
    (allPlain_noBullet d)
  intro x y hx hy
  exact (hmono x hx).trans (hmono y hy).symm

end DualTree.MixedProduct
