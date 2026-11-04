import DualTree.ShiftedRaySlots
import DualTree.RayHalesJewett

/-!
# A genuine shifted one-root Hales–Jewett tree variable word

The established disjoint-slot decoder places each D₀ coordinate's flat
Hales–Jewett word in its own interval of N ray positions.  Unlike a
pointwise pushforward of the old ray word, the definition below checks
the source-facing `VariableWord.atRoot` and `VariableWord.below`
obligations on ACTUAL bounded nodes.

The support consists of the first variable occurrence r in that
coordinate's translated interval.  The variable is evaluated
independently of other coordinates; outside the interval every word
symbol is the supplied fallback constant.

At intrinsic height one the singleton support is truly complete-skew.
An exact evaluation and span description connects this tree word to
the full flat Hales–Jewett line. The construction by itself makes no
c-goodness claim and supplies no D₁ leaf data.
-/

namespace DualTree.ShiftedRayWord

open DualTree.ShiftedRaySlots
open DualTree.InterleavedHeightOne
open DualTree.RayHalesJewett

/-- The genuine singleton support name in coordinate i's ray interval. -/
def rootVar {b N d : Nat} (hb : 0 < b)
    (i : Fin d) (r : Fin N) :
    {t : BoundedNode b (ambient d N) // t ∈ [slotPos hb i r]} :=
  ⟨slotPos hb i r, by simp⟩

/-- Translate the flat word into the i-th disjoint ray interval.
Every variable symbol uses the ACTUAL selected first-root name. -/
noncomputable def symbol
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (i : Fin d)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N)
    (t : BoundedNode b (ambient d N)) :
    Sum β {s : BoundedNode b (ambient d N) //
      s ∈ [slotPos hb i r]} :=
  match slotIndex hb i t with
  | none => Sum.inl fallback
  | some j =>
      match w j with
      | Sum.inl a => Sum.inl a
      | Sum.inr _ => Sum.inr (rootVar hb i r)

/-- The root carries its genuine variable symbol. -/
theorem symbol_at_root
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (i : Fin d)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N) (hroot : w r = Sum.inr 0) :
    symbol hb i w fallback r (slotPos hb i r) =
      Sum.inr (rootVar hb i r) := by
  simp [symbol, slotIndex_slotPos, hroot]

/-- Any occurrence of the singleton variable is a descendant of its
selected root, using the TRUE inverse slot decoder and first-variable
position inequality, not an assumed tree-word legality predicate. -/
theorem symbol_below
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (i : Fin d)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (v : {s : BoundedNode b (ambient d N) //
      s ∈ [slotPos hb i r]})
    (t : BoundedNode b (ambient d N))
    (hv : symbol hb i w fallback r t = Sum.inr v) :
    IsPrefix v.1.1 t.1 := by
  cases hi : slotIndex hb i t with
  | none =>
      simp [symbol, hi] at hv
  | some j =>
      cases hw : w j with
      | inl a =>
          simp [symbol, hi, hw] at hv
      | inr u =>
          have hname : rootVar hb i r = v := by
            simpa [symbol, hi, hw] using hv
          have hpos : t = slotPos hb i j :=
            slotIndex_some hb i t j hi
          have hrootNode : v.1 = slotPos hb i r :=
            congrArg Subtype.val hname.symm
          have hle : r.val ≤ j.val := hfirst j u hw
          change IsPrefix v.1.1 t.1
          rw [hrootNode, hpos]
          exact zeroRay_prefix hb
            (offset N i + r.val) (offset N i + j.val)
            (Nat.add_le_add_left hle _)

/-- A LEGAL source-facing one-variable word on the complete ambient
tree; the unique root lies in the i-th scheduled interval. -/
noncomputable def variableWord
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (i : Fin d)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    VariableWord b (ambient d N) β where
  support := [slotPos hb i r]
  support_nodup := by simp
  word := symbol hb i w fallback r
  atRoot := by
    intro v
    have hname : v = rootVar hb i r := by
      apply Subtype.ext
      change v.1 = slotPos hb i r
      simpa using v.2
    subst v
    exact symbol_at_root hb i w fallback r hroot
  below := by
    intro v t ht
    exact symbol_below hb i w fallback r hfirst v t ht

/-- Genuine height-one complete-skew support, not a dummy singleton. -/
noncomputable def kWord
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (i : Fin d)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    KVariableWord b (ambient d N) 1 β
      (SkewTree.forwardAuxB (b := b)) where
  toVariableWord := variableWord hb i w fallback r hroot hfirst
  complete_support := by
    change SkewTree.completeB SkewTree.forwardAuxB 1
      [slotNode hb i r] = true
    exact SkewTree.singleton_complete_oneB _ _

/-- The full tree-word embedding of a flat coordinate word at its
own interval, with fallback letters outside all its slots. -/
noncomputable def embed
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (i : Fin d)
    (fallback : β) (u : Fin N → β) :
    TreeWord b (ambient d N) β :=
  fun t =>
    match slotIndex hb i t with
    | none => fallback
    | some j => u j

/-- Exact evaluation on the actual ambient tree, including non-slot
positions, constant flat symbols and ALL true variable occurrences. -/
theorem variableWord_eval
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (i : Fin d)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j)
    (σ : (variableWord hb i w fallback r hroot hfirst).Vars → β) :
    (variableWord hb i w fallback r hroot hfirst).eval σ =
      embed hb i fallback
        (SpanAudit.eval w (fun _ => σ (rootVar hb i r))) := by
  funext t
  change SpanAudit.eval (symbol hb i w fallback r) σ t =
    embed hb i fallback
      (SpanAudit.eval w (fun _ => σ (rootVar hb i r))) t
  cases hi : slotIndex hb i t with
  | none =>
      simp [symbol, embed, SpanAudit.eval, SpanAudit.evalSymbol, hi]
  | some j =>
      cases hw : w j with
      | inl a =>
          simp [symbol, embed, SpanAudit.eval, SpanAudit.evalSymbol, hi, hw]
      | inr v =>
          simp [symbol, embed, SpanAudit.eval, SpanAudit.evalSymbol, hi, hw]

/-- The actual support list is precisely the scheduled ray root. -/
theorem kWord_supportNodes
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (i : Fin d)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    (kWord hb i w fallback r hroot hfirst).toVariableWord.supportNodes =
      [slotNode hb i r] := by
  rfl

/-- The FULL evaluated span of the true tree-variable word
is exactly the flat Hales–Jewett line embedded in this interval. -/
theorem kWord_span_eq_flat_range
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (i : Fin d)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    (kWord hb i w fallback r hroot hfirst).span =
      Set.range (fun a : β =>
        embed hb i fallback (SpanAudit.eval w (fun _ => a))) := by
  ext u
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ (rootVar hb i r), ?_⟩
    exact (variableWord_eval hb i w fallback r hroot hfirst σ).symm.trans hσ
  · rintro ⟨a, rfl⟩
    let σ : (variableWord hb i w fallback r hroot hfirst).Vars → β :=
      fun _ => a
    refine ⟨σ, ?_⟩
    simpa [σ] using variableWord_eval hb i w fallback r hroot hfirst σ

/-- There is always a real evaluated tree word in the span,
even with one original alphabet letter. -/
theorem kWord_span_nonempty
    {b N d : Nat} {β : Type*}
    (hb : 0 < b) (i : Fin d)
    (w : Fin N → Sum β (Fin 1)) (fallback : β)
    (r : Fin N)
    (hroot : w r = Sum.inr 0)
    (hfirst : ∀ j : Fin N, ∀ v : Fin 1,
      w j = Sum.inr v → r ≤ j) :
    ((kWord hb i w fallback r hroot hfirst).span).Nonempty := by
  let σ : (variableWord hb i w fallback r hroot hfirst).Vars → β :=
    fun _ => fallback
  refine ⟨(variableWord hb i w fallback r hroot hfirst).eval σ, ?_⟩
  exact ⟨σ, rfl⟩

end DualTree.ShiftedRayWord
