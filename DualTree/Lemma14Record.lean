import DualTree.Lemma14Invariant

/-!
# Canonical record behind Proposition 15

Lemma 14 says that, in the D2=empty case, the color is determined by the D1
leaf together with the values of the corresponding word on the predecessor
chain of that leaf.

Proposition 15 encodes this information into a finite Hales--Jewett word via
an operator Q. Before formalizing that finite coding, we package the invariant
itself as a canonical record and prove that equality of records is exactly the
Lemma 14 relation.
-/

namespace DualTree.MixedProduct

/--
For every D1/up coordinate, record the selected leaf and the word restricted
to nodes lying on its predecessor chain. Values off the chain are hidden.
-/
def upTraceRecord
    {b n d : Nat} {α : Type*}
    {kind : Fin d → CoordKind}
    (x : Element b n d α kind) :
    UpIndex kind →
      (LeafNode b n × (BoundedNode b n → Option α)) :=
  fun i =>
    (x.upPoint i,
      fun t =>
        if IsPrefix t.1 (x.upPoint i).1
        then some (x.words i.1 t)
        else none)

theorem sameUpTrace_iff_record_eq
    {b n d : Nat} {α : Type*}
    {kind : Fin d → CoordKind}
    (x y : Element b n d α kind) :
    SameUpTrace x y ↔ upTraceRecord x = upTraceRecord y := by
  constructor
  · rintro ⟨hpoint, hword⟩
    funext i
    apply Prod.ext
    · exact hpoint i
    · funext t
      have hp : x.upPoint i = y.upPoint i := hpoint i
      by_cases hpre : IsPrefix t.1 (x.upPoint i).1
      · have hw := hword i t hpre
        simp [upTraceRecord, hp, hpre, hw]
      · have hpre' : ¬ IsPrefix t.1 (y.upPoint i).1 := by
          simpa [hp] using hpre
        simp [upTraceRecord, hpre, hpre']
  · intro hrec
    constructor
    · intro i
      exact congrArg Prod.fst (congrFun hrec i)
    · intro i t hpre
      have hp : x.upPoint i = y.upPoint i :=
        congrArg Prod.fst (congrFun hrec i)
      have hpre' : IsPrefix t.1 (y.upPoint i).1 := by
        simpa [hp] using hpre
      have hv :=
        congrArg (fun r => (r i).2 t) hrec
      simpa [upTraceRecord, hpre, hpre'] using hv

/--
Equivalent factorization form of the Lemma 14 invariant: on the generated
span, the color is constant on fibers of the canonical up-trace record.
-/
theorem upCanonical_iff_same_record
    {b n d k : Nat} {α γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (c : Element b n d α kind → γ)
    (f : VariableWord b n d k α aux kind) :
    UpCanonical c f ↔
      ∀ ⦃x y : Element b n d α kind⦄,
        x ∈ f.span →
        y ∈ f.span →
        upTraceRecord x = upTraceRecord y →
        c x = c y := by
  constructor
  · intro h x y hx hy hrec
    exact h hx hy ((sameUpTrace_iff_record_eq x y).2 hrec)
  · intro h x y hx hy htrace
    exact h hx hy ((sameUpTrace_iff_record_eq x y).1 htrace)

/-- A canonical subspace factors through the up-trace record. -/
theorem color_eq_of_upCanonical_of_same_record
    {b n d k : Nat} {α γ : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    {c : Element b n d α kind → γ}
    {f : VariableWord b n d k α aux kind}
    (hcanon : UpCanonical c f)
    {x y : Element b n d α kind}
    (hx : x ∈ f.span)
    (hy : y ∈ f.span)
    (hrec : upTraceRecord x = upTraceRecord y) :
    c x = c y :=
  (upCanonical_iff_same_record c f).1 hcanon hx hy hrec

end DualTree.MixedProduct
