import DualTree.KVariableWord

/-!
# Padding actual tree words to a larger ambient height

Keep every old node and symbol, and put a fixed alphabet letter at all
new nodes. The variable roots retain their actual ambient names. Their
list of unbounded nodes is unchanged, so every complete-skew support
certificate is preserved, for either auxiliary-order convention.

The evaluation and span theorems are exact and do not assume two letters.
They transport an ordinary ground-word Ramsey theorem to every larger
ambient height. No starred-object lifting, canonical-model transport,
or relative Ramsey conclusion is asserted by this construction.
-/

namespace DualTree.AmbientHeightPadding

/-- Inclusion of the smaller finite homogeneous tree in the larger one. -/
def includeNode {b n N : Nat} (h : n ≤ N)
    (s : BoundedNode b n) : BoundedNode b N :=
  ⟨s.1, lt_of_lt_of_le s.2 h⟩

theorem includeNode_injective {b n N : Nat} (h : n ≤ N) :
    Function.Injective (includeNode (b := b) h) := by
  intro s t hst
  exact Subtype.ext (congrArg (fun x : BoundedNode b N => x.1) hst)

/-- Padding a constant word fixes all newly added nodes to one letter. -/
def padTreeWord {b n N : Nat} {α : Type*}
    (_h : n ≤ N) (fallback : α) (w : TreeWord b n α) : TreeWord b N α :=
  fun s =>
    letI : Decidable (InHomTree n s.1) :=
      inferInstanceAs (Decidable (s.1.length < n))
    if hs : InHomTree n s.1 then w ⟨s.1, hs⟩ else fallback

/-- The new root-name type, with no new roots added by padding. -/
abbrev PaddedVars {b n N : Nat} {α : Type*}
    (f : VariableWord b n α) (h : n ≤ N) :=
  {s : BoundedNode b N // s ∈ f.support.map (includeNode h)}

/-- Padding changes only the bound proof of a root, not its node. -/
def rootEquiv {b n N : Nat} {α : Type*}
    (f : VariableWord b n α) (h : n ≤ N) : f.Vars ≃ PaddedVars f h where
  toFun v := ⟨includeNode h v.1, List.mem_map.mpr ⟨v.1, v.2, rfl⟩⟩
  invFun v := by
    have hsmall : InHomTree n v.1.1 := by
      obtain ⟨s, _, hsv⟩ := List.mem_map.mp v.2
      have hnode : s.1 = v.1.1 :=
        congrArg (fun x : BoundedNode b N => x.1) hsv
      simpa only [hnode] using s.2
    refine ⟨⟨v.1.1, hsmall⟩, ?_⟩
    obtain ⟨s, hs, hsv⟩ := List.mem_map.mp v.2
    have heq : s = (⟨v.1.1, hsmall⟩ : BoundedNode b n) :=
      Subtype.ext (congrArg (fun x : BoundedNode b N => x.1) hsv)
    simpa only [heq] using hs
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Old symbols use transported root names; every new position is constant. -/
def padSymbol {b n N : Nat} {α : Type*}
    (f : VariableWord b n α) (h : n ≤ N) (fallback : α)
    (s : BoundedNode b N) : Sum α (PaddedVars f h) :=
  letI : Decidable (InHomTree n s.1) :=
    inferInstanceAs (Decidable (s.1.length < n))
  if hs : InHomTree n s.1 then
    match f.word ⟨s.1, hs⟩ with
    | Sum.inl a => Sum.inl a
    | Sum.inr v => Sum.inr (rootEquiv f h v)
  else Sum.inl fallback

/-- Padding is a genuine legal variable word, with exactly the old roots. -/
def padVariableWord {b n N : Nat} {α : Type*}
    (f : VariableWord b n α) (h : n ≤ N) (fallback : α) :
    VariableWord b N α where
  support := f.support.map (includeNode h)
  support_nodup := f.support_nodup.map (includeNode_injective h)
  word := padSymbol f h fallback
  atRoot := by
    intro v
    let old : f.Vars := (rootEquiv f h).symm v
    have hv : rootEquiv f h old = v := (rootEquiv f h).apply_symm_apply v
    have hval : includeNode h old.1 = v.1 := congrArg Subtype.val hv
    have hsmall : InHomTree n v.1.1 := by
      have hnode : old.1.1 = v.1.1 :=
        congrArg (fun x : BoundedNode b N => x.1) hval
      simpa only [hnode] using old.1.2
    have hsmallNode : (⟨v.1.1, hsmall⟩ : BoundedNode b n) = old.1 :=
      Subtype.ext (congrArg (fun x : BoundedNode b N => x.1) hval).symm
    have hw : f.word ⟨v.1.1, hsmall⟩ = Sum.inr old := by
      rw [hsmallNode]
      exact f.atRoot old
    simp [padSymbol, hsmall, hw, hv]
  below := by
    intro v s hs
    by_cases hsmall : InHomTree n s.1
    · cases hw : f.word ⟨s.1, hsmall⟩ with
      | inl a => simp [padSymbol, hsmall, hw] at hs
      | inr old =>
          have hv : rootEquiv f h old = v := by
            simpa [padSymbol, hsmall, hw] using hs
          have hnode := congrArg (fun z : PaddedVars f h => z.1.1) hv
          change old.1.1 = v.1.1 at hnode
          have hprefix := f.below old ⟨s.1, hsmall⟩ hw
          simpa only [hnode] using hprefix
    · simp [padSymbol, hsmall] at hs

/-- The actual root-node list is unchanged, including its order. -/
theorem padVariableWord_supportNodes
    {b n N : Nat} {α : Type*}
    (f : VariableWord b n α) (h : n ≤ N) (fallback : α) :
    (padVariableWord f h fallback).supportNodes = f.supportNodes := by
  change (f.support.map (includeNode h)).map Subtype.val =
    f.support.map Subtype.val
  rw [List.map_map]
  rfl

/-- Exact evaluation for every assignment to the padded roots. -/
theorem padVariableWord_eval
    {b n N : Nat} {α : Type*}
    (f : VariableWord b n α) (h : n ≤ N) (fallback : α)
    (σ : (padVariableWord f h fallback).Vars → α) :
    (padVariableWord f h fallback).eval σ =
      padTreeWord h fallback (f.eval (fun v => σ (rootEquiv f h v))) := by
  funext s
  by_cases hsmall : InHomTree n s.1
  · cases hw : f.word ⟨s.1, hsmall⟩ <;>
      simp [VariableWord.eval, padVariableWord, padSymbol, padTreeWord,
        SpanAudit.eval, SpanAudit.evalSymbol, hsmall, hw]
  · simp [VariableWord.eval, padVariableWord, padSymbol, padTreeWord,
      SpanAudit.eval, SpanAudit.evalSymbol, hsmall]

/-- Padding carries the whole evaluated span exactly onto the new span. -/
theorem padVariableWord_span
    {b n N : Nat} {α : Type*}
    (f : VariableWord b n α) (h : n ≤ N) (fallback : α) :
    (padVariableWord f h fallback).span =
      (padTreeWord h fallback) '' f.span := by
  ext w
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨f.eval (fun v => σ (rootEquiv f h v)), ⟨_, rfl⟩, ?_⟩
    exact (padVariableWord_eval f h fallback σ).symm.trans hσ
  · rintro ⟨u, ⟨σ, hσ⟩, hu⟩
    refine ⟨fun v => σ ((rootEquiv f h).symm v), ?_⟩
    calc
      _ = padTreeWord h fallback
          (f.eval (fun v => σ ((rootEquiv f h).symm (rootEquiv f h v)))) :=
        padVariableWord_eval f h fallback _
      _ = padTreeWord h fallback (f.eval σ) := by
        apply congrArg (padTreeWord h fallback)
        apply congrArg f.eval
        funext v
        exact congrArg σ ((rootEquiv f h).symm_apply_apply v)
      _ = padTreeWord h fallback u := congrArg (padTreeWord h fallback) hσ
      _ = w := hu

/-- Complete-skew geometry is preserved for the original auxiliary order
and the original intrinsic complete height. -/
def padCompleteWord {b n N k : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    (f : KVariableWord b n k α aux) (h : n ≤ N) (fallback : α) :
    KVariableWord b N k α aux where
  toVariableWord := padVariableWord f.toVariableWord h fallback
  complete_support := by
    rw [padVariableWord_supportNodes]
    exact f.complete_support

theorem padCompleteWord_span
    {b n N k : Nat} {α : Type*} {aux : Node b → Node b → Bool}
    (f : KVariableWord b n k α aux) (h : n ≤ N) (fallback : α) :
    (padCompleteWord f h fallback).span = (padTreeWord h fallback) '' f.span :=
  padVariableWord_span f.toVariableWord h fallback

/-- Any proved ordinary ground-word Ramsey statement persists at every
larger ambient height. Both the target complete word and its whole
monochromatic span are constructed, rather than assumed to lift. -/
theorem ground_word_ramsey_mono
    {b n N k : Nat} {α γ : Type*} {aux : Node b → Node b → Bool}
    (h : n ≤ N) (fallback : α)
    (hRamsey : ∀ c : TreeWord b n α → γ,
      ∃ f : KVariableWord b n k α aux,
        ∃ col : γ, ∀ w : TreeWord b n α, w ∈ f.span → c w = col) :
    ∀ c : TreeWord b N α → γ,
      ∃ f : KVariableWord b N k α aux,
        ∃ col : γ, ∀ w : TreeWord b N α, w ∈ f.span → c w = col := by
  intro c
  obtain ⟨f, col, hmono⟩ := hRamsey (fun w => c (padTreeWord h fallback w))
  refine ⟨padCompleteWord f h fallback, col, ?_⟩
  intro w hw
  rw [padCompleteWord_span] at hw
  obtain ⟨u, hu, heq⟩ := hw
  simpa only [heq] using hmono u hu

end DualTree.AmbientHeightPadding
