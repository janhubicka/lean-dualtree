import DualTree.AllPlainMixedRamsey

/-!
# Unconditional c-goodness in the D₂-only height-one base case

Here ALL mixed-product coordinates have kind `bullet` (D₂), and
the ambient tree is b^{<1}, whose only node is the empty root.
Every point marker must therefore equal that root. Equality of
the observed bullet letters consequently determines every
coordinate tree word and the whole mixed element, independently
of its chosen variable word.

In particular Definition 11's c-goodness is automatic at
ambient height one for an all-D₂ kind. We also construct an
ACTUAL mixed variable word with intrinsic dimension one:
every component has the singleton empty-root support, so the
full vector-complete-skew condition holds. D₁ leaf data are
eliminated by genuinely empty up-index types, not fabricated.

This is a useful marked-coordinate base case, not
monochromaticity of a D₂ starred span: the colouring may
freely depend on the observed D₂ letters. It does NOT
establish mixed Ramsey existence with both D₀ and D₂
coordinates or with higher intrinsic dimensions.
-/

namespace DualTree.MixedProduct.AllBulletRamsey

/-- Exactly the D₂ coordinates. -/
def allBulletKind (d : Nat) : Fin d → CoordKind :=
  fun _ => CoordKind.bullet

/-- The one actual bounded node of b^{<1}. -/
def root (b : Nat) : BoundedNode b 1 :=
  ⟨[], by simp [InHomTree]⟩

theorem node_eq_root {b : Nat} (t : BoundedNode b 1) :
    t = root b := by
  rcases t with ⟨s, hs⟩
  apply Subtype.ext
  dsimp [root]
  cases s with
  | nil => rfl
  | cons a s => simp [InHomTree] at hs

/-- Genuine singleton support name for the empty-root variable. -/
def rootVar (b : Nat) :
    {t : BoundedNode b 1 // t ∈ [root b]} :=
  ⟨root b, by simp⟩

/-- A legal tree variable word on the genuine height-one
ambient tree. Its only variable is at the unique root. -/
def oneRootVariableWord (b : Nat) (β : Type*) :
    DualTree.VariableWord b 1 β where
  support := [root b]
  support_nodup := by simp
  word := fun _ => Sum.inr (rootVar b)
  atRoot := by
    intro v
    have hv : v = rootVar b := by
      apply Subtype.ext
      change v.1 = root b
      simpa using v.2
    subst v
    rfl
  below := by
    intro v t _
    have hv : v.1 = root b := by
      simpa using v.2
    have hr : v.1.1 = ([] : Node b) := by
      rw [hv]
      rfl
    rw [hr]
    exact ⟨t.1, by simp⟩

/-- The singleton root support is 1-complete skew. -/
def oneRootKVariableWord (b : Nat) (β : Type*) :
    KVariableWord b 1 1 β (SkewTree.forwardAuxB (b := b)) where
  toVariableWord := oneRootVariableWord b β
  complete_support := by
    change SkewTree.completeB SkewTree.forwardAuxB 1
      [([] : Node b)] = true
    exact SkewTree.singleton_complete_oneB _ _

/-- Every component shares the singleton actual root; the
entire vector 1-complete skew predicate is checked. -/
def oneRootVectorWord (b d : Nat) (β : Type*) :
    VectorVariableWord b 1 d 1 β (SkewTree.forwardAuxB (b := b)) where
  components := fun _ => oneRootKVariableWord b β
  vector_complete := by
    change VectorSkew.vectorCompleteB SkewTree.forwardAuxB 1
      (fun _ : Fin d => [([] : Node b)]) = true
    exact VectorSkew.identical_singletons_vectorComplete_one _ _

/-- The corresponding actual all-D₂ mixed-product variable word.
The D₁ index type is empty and contributes no fake leaf data. -/
def oneRootAllBulletMixedWord (b d : Nat) (β : Type*) :
    VariableWord b 1 d 1 β
      (SkewTree.forwardAuxB (b := b)) (allBulletKind d) where
  vector := oneRootVectorWord b d β
  upLeaves := fun i => nomatch i.2
  upLeaves_nodup := fun i => nomatch i.2
  upLeaves_card := fun i => nomatch i.2
  up_support_skew := fun i => nomatch i.2

/-- In an all-D₂ height-one product, equality of the marked
root-letter observations forces equality of the ENTIRE
mixed-product elements. It does not require membership in any
specific variable-word span. -/
theorem eq_of_equal_marked_letters
    {b d : Nat} {β : Type*}
    (x y : Element b 1 d β (allBulletKind d))
    (hletters : ∀ i : BulletIndex (allBulletKind d),
      x.words i.1 (x.bulletPoint i) =
        y.words i.1 (y.bulletPoint i)) :
    x = y := by
  have hwords : x.words = y.words := by
    funext j t
    let i : BulletIndex (allBulletKind d) := ⟨j, rfl⟩
    have h := hletters i
    have hx : x.bulletPoint i = root b := node_eq_root _
    have hy : y.bulletPoint i = root b := node_eq_root _
    have ht : t = root b := node_eq_root t
    change
      x.words j (x.bulletPoint i) =
        y.words j (y.bulletPoint i) at h
    simpa only [hx, hy, ht] using h
  have hup : x.upPoint = y.upPoint := by
    funext i
    cases i.2
  have hbullet : x.bulletPoint = y.bulletPoint := by
    funext i
    calc
      x.bulletPoint i = root b := node_eq_root _
      _ = y.bulletPoint i := (node_eq_root _).symm
  cases x with
  | mk wx ux bx =>
    cases y with
    | mk wy uy byy =>
      change wx = wy at hwords
      change ux = uy at hup
      change bx = byy at hbullet
      cases hwords
      cases hup
      cases hbullet
      rfl

/-- For EVERY all-D₂ mixed word at ambient height one,
every colouring is Definition-11 c-good. Its colour is
already allowed to depend on the observed D₂ root letters.
This is a genuine statement about the *mixed* Element type. -/
theorem good_allBullet_at_height_one
    {b d k : Nat} {β γ : Type*}
    {aux : Node b → Node b → Bool}
    (f : VariableWord b 1 d k β aux (allBulletKind d))
    (color : Element b 1 d β (allBulletKind d) → γ) :
    Good color f := by
  intro x y _ _ _ hletters
  exact congrArg color (eq_of_equal_marked_letters x y hletters)

/-- An unconditional existence theorem in the genuine mixed
product for all-D₂ coordinates, at intrinsic complete-skew
dimension one. The witness is explicit and works for ANY
alphabet and ANY colouring type (no finite-color hypothesis),
since Definition 11 permits dependence on all D₂ letters. -/
theorem exists_good_allBullet_height_one
    (b d : Nat) (β γ : Type*) :
    ∀ color : Element b 1 d β (allBulletKind d) → γ,
      ∃ f : VariableWord b 1 d 1 β
          (SkewTree.forwardAuxB (b := b)) (allBulletKind d),
        Good color f := by
  intro color
  exact ⟨oneRootAllBulletMixedWord b d β,
    good_allBullet_at_height_one
      (oneRootAllBulletMixedWord b d β) color⟩

end DualTree.MixedProduct.AllBulletRamsey
