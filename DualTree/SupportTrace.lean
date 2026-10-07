import DualTree.Lemma14Record

/-!
# Variable-root trace of a word along a chosen leaf

The operator Q in Proposition 15 records, for every D1 coordinate, the selected
leaf and the letters at the variable-root predecessors of that leaf.  The
preceding Lemma14Record file kept values at *all* ambient predecessors.

This file proves the missing algebraic bridge: for words in the span of f,
agreement at roots of f along a leaf already forces agreement at every
ambient predecessor of that leaf.  It is independent of the size of the
alphabet and of the skew-tree order.
-/

namespace DualTree.MixedProduct

/--
If two evaluations of one tree-variable word agree at every variable root
below a chosen leaf, then they agree along its entire predecessor chain.
-/
theorem prefix_values_eq_of_root_values_eq
    {b n : Nat} {α : Type*}
    (f : DualTree.VariableWord b n α)
    (u v : TreeWord b n α)
    (hu : u ∈ f.span) (hv : v ∈ f.span)
    (leaf : LeafNode b n)
    (hroots : ∀ r : f.Vars, IsPrefix r.1.1 leaf.1 → u r.1 = v r.1) :
    ∀ t : BoundedNode b n, IsPrefix t.1 leaf.1 → u t = v t := by
  rcases hu with ⟨σu, hσu⟩
  rcases hv with ⟨σv, hσv⟩
  intro t ht
  cases hft : f.word t with
  | inl a =>
      have hut : u t = a := by
        rw [← hσu]
        simp [SpanAudit.eval, SpanAudit.evalSymbol, hft]
      have hvt : v t = a := by
        rw [← hσv]
        simp [SpanAudit.eval, SpanAudit.evalSymbol, hft]
      exact hut.trans hvt.symm
  | inr r =>
      have hrpre : IsPrefix r.1.1 leaf.1 :=
        isPrefix_trans (f.below r t hft) ht
      have hroot := hroots r hrpre
      have hut : u t = u r.1 := by
        rw [← hσu]
        simp [SpanAudit.eval, SpanAudit.evalSymbol, hft, f.atRoot r]
      have hvt : v t = v r.1 := by
        rw [← hσv]
        simp [SpanAudit.eval, SpanAudit.evalSymbol, hft, f.atRoot r]
      exact hut.trans (hroot.trans hvt.symm)

/--
The smaller Q-record: the selected leaf, and the letters at source variable
roots that precede it.  None marks roots outside its predecessor chain.
-/
noncomputable def supportTraceRecord
    {b n d k : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k α aux kind)
    (x : Element b n d α kind) :
    (i : UpIndex kind) →
      (LeafNode b n × ((f.vector.components i.1).Vars → Option α)) := by
  classical
  exact fun i =>
    (x.upPoint i,
      fun r =>
        if IsPrefix r.1.1 (x.upPoint i).1
        then some (x.words i.1 r.1)
        else none)

/--
On a fixed mixed span, equality of the root trace is equivalent to the exact
Lemma 14 comparison of all predecessor values.
-/
theorem sameUpTrace_iff_supportTraceRecord_eq_of_mem_span
    {b n d k : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k α aux kind)
    (x y : Element b n d α kind)
    (hx : x ∈ f.span) (hy : y ∈ f.span) :
    SameUpTrace x y ↔ supportTraceRecord f x = supportTraceRecord f y := by
  classical
  constructor
  · rintro ⟨hpoint, hword⟩
    funext i
    apply Prod.ext
    · exact hpoint i
    · funext r
      have hp : x.upPoint i = y.upPoint i := hpoint i
      by_cases hpre : IsPrefix r.1.1 (x.upPoint i).1
      · have hpre' : IsPrefix r.1.1 (y.upPoint i).1 := by
          simpa [hp] using hpre
        have hw := hword i r.1 hpre
        simp [supportTraceRecord, hpre, hpre', hw]
      · have hpre' : ¬ IsPrefix r.1.1 (y.upPoint i).1 := by
          simpa [hp] using hpre
        simp [supportTraceRecord, hpre, hpre']
  · intro hrec
    constructor
    · intro i
      exact congrArg Prod.fst (congrFun hrec i)
    · intro i t hpre
      have hp : x.upPoint i = y.upPoint i :=
        congrArg Prod.fst (congrFun hrec i)
      let g := (f.vector.components i.1).toVariableWord
      have hroots : ∀ r : g.Vars,
          IsPrefix r.1.1 (x.upPoint i).1 →
          x.words i.1 r.1 = y.words i.1 r.1 := by
        intro r hr
        have hr' : IsPrefix r.1.1 (y.upPoint i).1 := by
          simpa [hp] using hr
        have hi : supportTraceRecord f x i = supportTraceRecord f y i :=
          congrFun hrec i
        have heq :
            (supportTraceRecord f x i).2 r =
              (supportTraceRecord f y i).2 r :=
          congrFun (congrArg Prod.snd hi) r
        change
          (if IsPrefix r.1.1 (x.upPoint i).1
            then some (x.words i.1 r.1) else none) =
          (if IsPrefix r.1.1 (y.upPoint i).1
            then some (y.words i.1 r.1) else none) at heq
        rw [if_pos hr, if_pos hr'] at heq
        exact Option.some.inj heq
      exact prefix_values_eq_of_root_values_eq g
        (x.words i.1) (y.words i.1) (hx.1 i.1) (hy.1 i.1)
        (x.upPoint i) hroots t hpre

/--
Proposition 15's pre-Hales--Jewett factorization, with only source variable
roots retained.  This does not yet prove that the finite direction coding
Q of Proposition 15 is onto.
-/
theorem upCanonical_iff_same_supportTraceRecord
    {b n d k : Nat} {α γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (c : Element b n d α kind → γ)
    (f : VariableWord b n d k α aux kind) :
    UpCanonical c f ↔
      ∀ ⦃x y : Element b n d α kind⦄,
        x ∈ f.span → y ∈ f.span →
        supportTraceRecord f x = supportTraceRecord f y →
        c x = c y := by
  constructor
  · intro h x y hx hy hrec
    exact h hx hy
      ((sameUpTrace_iff_supportTraceRecord_eq_of_mem_span f x y hx hy).2 hrec)
  · intro h x y hx hy htrace
    exact h hx hy
      ((sameUpTrace_iff_supportTraceRecord_eq_of_mem_span f x y hx hy).1 htrace)

end DualTree.MixedProduct
