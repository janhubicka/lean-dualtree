import DualTree.HigherSkewGeometry
import DualTree.KVariableWord
import DualTree.MixedProduct

/-!
# Track C: an actual legal height-two variable word with independent roots

The star certificates in HigherSkewGeometry describe finite node supports.
Here we construct actual bounded support variables and a source-facing
VariableWord. Each variable occurs at its own root and nowhere else.
Consequently the evaluated span is a *genuine nonempty rectangular family*
whose assignments are recovered independently at those support nodes.

This is a geometric and exact-span witness, not yet a Ramsey existence
theorem for arbitrary colourings. HJ root/cone substitutions will replace
the singleton-occurrence word in a subsequent construction.
-/

namespace DualTree.HigherSkewWord

open DualTree.UpLeafGeometry

/-- Embed a root from b^{<n} into the next ambient height. -/
def boundedRoot {b n : Nat} (r : BoundedNode b n) :
    BoundedNode b (n + 1) :=
  ⟨r.1, by
    change r.1.length < n + 1
    have hr : r.1.length < n := r.2
    omega⟩

/-- Embed the selected depth-n child into the tree b^{<n+1}. -/
def boundedChild {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) (i : Fin b) :
    BoundedNode b (n + 1) :=
  ⟨(ambientLeaf hb r i).1, by
    change (ambientLeaf hb r i).1.length < n + 1
    rw [(ambientLeaf hb r i).2]
    omega⟩

/-- Actual bounded support: one root and all b distinct children. -/
def support {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) : List (BoundedNode b (n + 1)) :=
  boundedRoot r :: List.ofFn (boundedChild hb r)

theorem support_nodup {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) : (support hb r).Nodup := by
  change (boundedRoot r :: List.ofFn (boundedChild hb r)).Nodup
  apply List.nodup_cons.mpr
  constructor
  · intro hm
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
    have hlen := congrArg
      (fun t : BoundedNode b (n + 1) => t.1.length) hi
    dsimp [boundedRoot, boundedChild] at hlen
    have hr : r.1.length < n := r.2
    have hchild : (ambientLeaf hb r i).1.length = n :=
      (ambientLeaf hb r i).2
    omega
  · apply List.nodup_ofFn.mpr
    intro i j hij
    apply ambientLeaf_val_injective hb r
    exact congrArg (fun t : BoundedNode b (n + 1) => t.1) hij

/-- Forget boundedness: exactly the certified ambient star, not a
singleton replacement. -/
theorem support_nodes {b n : Nat} (hb : 0 < b)
    (r : BoundedNode b n) :
    (support hb r).map Subtype.val =
      HigherSkewGeometry.ambientStar hb r := by
  simp [support, boundedRoot, boundedChild, HigherSkewGeometry.ambientStar,
    UpLeafGeometry.star, List.map_ofFn, Function.comp_def]

/-- Every actual support node carries its own variable; every other node
is assigned the same fixed letter. -/
noncomputable def symbol {b n : Nat} {β : Type*}
    (hb : 0 < b) (r : BoundedNode b n) (fallback : β)
    (t : BoundedNode b (n + 1)) :
    Sum β {u : BoundedNode b (n + 1) // u ∈ support hb r} :=
  if h : t ∈ support hb r then Sum.inr ⟨t, h⟩ else Sum.inl fallback

theorem symbol_at_root {b n : Nat} {β : Type*}
    (hb : 0 < b) (r : BoundedNode b n) (fallback : β)
    (v : {u : BoundedNode b (n + 1) // u ∈ support hb r}) :
    symbol hb r fallback v.1 = Sum.inr v := by
  classical
  simp [symbol, v.2]

theorem symbol_below {b n : Nat} {β : Type*}
    (hb : 0 < b) (r : BoundedNode b n) (fallback : β)
    (v : {u : BoundedNode b (n + 1) // u ∈ support hb r})
    (t : BoundedNode b (n + 1))
    (h : symbol hb r fallback t = Sum.inr v) :
    IsPrefix v.1.1 t.1 := by
  classical
  by_cases hm : t ∈ support hb r
  · have heq : (⟨t, hm⟩ : {u : BoundedNode b (n + 1) //
        u ∈ support hb r}) = v := by
      simpa [symbol, hm] using h
    have hnode : t.1 = v.1.1 :=
      congrArg (fun u : {x : BoundedNode b (n + 1) //
        x ∈ support hb r} => u.1.1) heq
    rw [hnode]
    exact isPrefix_refl _
  · simp [symbol, hm] at h

/-- A legal height-two word: its support is the true b-branching star.
At-root and below-root are verified from its actual symbols. -/
noncomputable def starWord {b n : Nat} {β : Type*}
    (hb : 0 < b) (r : BoundedNode b n) (fallback : β) :
    DualTree.VariableWord b (n + 1) β where
  support := support hb r
  support_nodup := support_nodup hb r
  word := symbol hb r fallback
  atRoot := by
    intro v
    exact symbol_at_root hb r fallback v
  below := by
    intro v t ht
    exact symbol_below hb r fallback v t ht

theorem starWord_supportNodes {b n : Nat} {β : Type*}
    (hb : 0 < b) (r : BoundedNode b n) (fallback : β) :
    (starWord hb r fallback).supportNodes =
      HigherSkewGeometry.ambientStar hb r := by
  simpa [DualTree.VariableWord.supportNodes, starWord] using
    support_nodes hb r

/-- Source-facing 2-complete variable word, forward-order convention. -/
noncomputable def starKWordForward {b n : Nat} {β : Type*}
    (hb : 0 < b) (r : BoundedNode b n) (fallback : β) :
    KVariableWord b (n + 1) 2 β SkewTree.forwardAuxB where
  toVariableWord := starWord hb r fallback
  complete_support := by
    rw [starWord_supportNodes]
    exact HigherSkewGeometry.ambientStar_complete_forward hb r

/-- Source-facing 2-complete variable word, printed order. -/
noncomputable def starKWordPaper {b n : Nat} {β : Type*}
    (hb : 0 < b) (r : BoundedNode b n) (fallback : β) :
    KVariableWord b (n + 1) 2 β SkewTree.paperAuxB where
  toVariableWord := starWord hb r fallback
  complete_support := by
    rw [starWord_supportNodes]
    exact HigherSkewGeometry.ambientStar_complete_paper hb r

/-- Each independent variable is recovered exactly by reading its own
support root. This is stronger than the nonemptiness of the span. -/
theorem starWord_eval_root {b n : Nat} {β : Type*}
    (hb : 0 < b) (r : BoundedNode b n) (fallback : β)
    (σ : (starWord hb r fallback).Vars → β)
    (v : (starWord hb r fallback).Vars) :
    (starWord hb r fallback).eval σ v.1 = σ v := by
  change SpanAudit.evalSymbol σ ((starWord hb r fallback).word v.1) = σ v
  rw [(starWord hb r fallback).atRoot v]
  rfl

/-- Independent substitutions at the b+1 genuine support roots cannot
collapse distinct parameter functions, even over a singleton alphabet. -/
theorem starWord_eval_injective {b n : Nat} {β : Type*}
    (hb : 0 < b) (r : BoundedNode b n) (fallback : β) :
    Function.Injective (fun σ : (starWord hb r fallback).Vars → β =>
      (starWord hb r fallback).eval σ) := by
  intro σ τ h
  funext v
  have hv : (starWord hb r fallback).eval σ v.1 =
      (starWord hb r fallback).eval τ v.1 := congrFun h v.1
  calc
    σ v = (starWord hb r fallback).eval σ v.1 :=
      (starWord_eval_root hb r fallback σ v).symm
    _ = (starWord hb r fallback).eval τ v.1 := hv
    _ = τ v := starWord_eval_root hb r fallback τ v

theorem starWord_span_nonempty {b n : Nat} {β : Type*}
    (hb : 0 < b) (r : BoundedNode b n) (fallback : β) :
    (starWord hb r fallback).span.Nonempty := by
  refine ⟨(starWord hb r fallback).eval (fun _ => fallback), ?_⟩
  exact ⟨fun _ => fallback, rfl⟩

/-- Identical genuine 2-complete supports in every coordinate, with
different letters freely assigned to different coordinates and roots. -/
noncomputable def vectorWordForward {b n d : Nat} {β : Type*}
    (hb : 0 < b) (r : BoundedNode b n) (fallback : β) :
    MixedProduct.VectorVariableWord b (n + 1) d 2 β
      SkewTree.forwardAuxB where
  components := fun _ => starKWordForward hb r fallback
  vector_complete := by
    change VectorSkew.vectorCompleteB SkewTree.forwardAuxB 2
      (fun _ : Fin d => (starWord hb r fallback).supportNodes) = true
    simp only [starWord_supportNodes]
    exact HigherSkewGeometry.ambientStar_vector_complete_forward
      (d := d) hb r

theorem vectorWordForward_span_nonempty {b n d : Nat} {β : Type*}
    (hb : 0 < b) (r : BoundedNode b n) (fallback : β) :
    (vectorWordForward (d := d) hb r fallback).span.Nonempty := by
  refine ⟨(fun _ : Fin d =>
    (starWord hb r fallback).eval (fun _ => fallback)), ?_⟩
  intro i
  exact ⟨fun _ => fallback, rfl⟩

end DualTree.HigherSkewWord
