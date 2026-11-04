import DualTree.InterleavedHeightOne

/-!
# Actual singleton variable word at a prescribed bounded root

The interleaved height-one geometry reserves a FIXED root for every D₂
coordinate, independent of the Hales–Jewett word eventually selected
for the D₀ coordinates. Here we construct the legal source-facing
KVariableWord at any such prescribed bounded node.

This word uses a genuine variable at the root and a supplied fallback
letter at every other ambient position. Its entire evaluated span is
EXACTLY the family of words taking an independent chosen letter at the
root. No Ramsey, smoothness or D₁ assertion is involved.

Unlike a flat "dummy marker", this is a real complete-skew variable
word at arbitrary finite ambient height. The algebra is independent of
the chosen node auxiliary order because every singleton is complete at
intrinsic height one.
-/

namespace DualTree.FixedRootMarkerWord

/-- The actual singleton support variable at the specified bounded node. -/
def rootVar {b n : Nat} (t : BoundedNode b n) :
    {s : BoundedNode b n // s ∈ [t]} :=
  ⟨t, by simp⟩

/-- Exactly one genuine variable at t, and a constant letter everywhere
else in the ambient tree. -/
noncomputable def variableWord
    {b n : Nat} {β : Type*}
    (t : BoundedNode b n) (fallback : β) :
    VariableWord b n β where
  support := [t]
  support_nodup := by simp
  word := fun x =>
    if hx : x = t then Sum.inr (rootVar t)
    else Sum.inl fallback
  atRoot := by
    intro v
    have hv : v.1 = t := by simpa using v.2
    have hveq : v = rootVar t := by
      apply Subtype.ext
      exact hv
    subst v
    simp [rootVar]
  below := by
    intro v x h
    by_cases hx : x = t
    · subst x
      have hv : v.1 = t := by simpa using v.2
      rw [hv]
      exact isPrefix_refl t.1
    · have hf : False := by
        simpa [hx] using h
      exact hf.elim

/-- The true singleton-root KVariableWord is 1-complete skew.
No fake support or synthetic leaf is introduced. -/
noncomputable def kWord
    {b n : Nat} {β : Type*}
    (t : BoundedNode b n) (fallback : β) :
    KVariableWord b n 1 β (SkewTree.forwardAuxB (b := b)) where
  toVariableWord := variableWord t fallback
  complete_support := by
    change SkewTree.completeB SkewTree.forwardAuxB 1
      [t.1] = true
    exact SkewTree.singleton_complete_oneB _ _

/-- The concrete tree word that remembers one letter at t. -/
noncomputable def valueWord
    {b n : Nat} {β : Type*}
    (t : BoundedNode b n) (fallback a : β) :
    TreeWord b n β :=
  fun x => if x = t then a else fallback

theorem valueWord_at_root
    {b n : Nat} {β : Type*}
    (t : BoundedNode b n) (fallback a : β) :
    valueWord t fallback a t = a := by
  simp [valueWord]

/-- Evaluation of the actual singleton variable word is exactly
the specified root letter plus constant off-root values. -/
theorem variableWord_eval
    {b n : Nat} {β : Type*}
    (t : BoundedNode b n) (fallback : β)
    (σ : (variableWord t fallback).Vars → β) :
    (variableWord t fallback).eval σ =
      valueWord t fallback (σ (rootVar t)) := by
  classical
  funext x
  by_cases hx : x = t
  · subst x
    simp [VariableWord.eval, SpanAudit.eval, SpanAudit.evalSymbol,
      variableWord, valueWord, rootVar]
  · simp [VariableWord.eval, SpanAudit.eval, SpanAudit.evalSymbol,
      variableWord, valueWord, hx]

/-- Every independently prescribed root letter really appears
as an evaluation of the true source-facing KVariableWord. -/
theorem valueWord_mem_span
    {b n : Nat} {β : Type*}
    (t : BoundedNode b n) (fallback a : β) :
    valueWord t fallback a ∈ (kWord t fallback).span := by
  let σ : (variableWord t fallback).Vars → β := fun _ => a
  change ∃ σ' : (variableWord t fallback).Vars → β,
    (variableWord t fallback).eval σ' = valueWord t fallback a
  refine ⟨σ, ?_⟩
  simpa [σ] using variableWord_eval t fallback σ

/-- Exact evaluated-span characterization for a fixed marked root:
no hidden coupling of the root letter to off-root constants. -/
theorem span_eq_range
    {b n : Nat} {β : Type*}
    (t : BoundedNode b n) (fallback : β) :
    (kWord t fallback).span =
      Set.range (valueWord t fallback) := by
  ext u
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ (rootVar t), ?_⟩
    exact (variableWord_eval t fallback σ).symm.trans hσ
  · rintro ⟨a, rfl⟩
    exact valueWord_mem_span t fallback a

/-- The marker span is explicitly nonempty with a supplied
alphabet letter, even if the original alphabet is singleton. -/
theorem span_nonempty
    {b n : Nat} {β : Type*}
    (t : BoundedNode b n) (fallback : β) :
    ((kWord t fallback).span).Nonempty :=
  ⟨valueWord t fallback fallback,
    valueWord_mem_span t fallback fallback⟩

end DualTree.FixedRootMarkerWord
