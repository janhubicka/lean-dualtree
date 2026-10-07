import DualTree.VariableWord
import DualTree.SkewTree

/-!
# Corollary 22: height-one audit

We formalize the smallest case from the referee audit:
  d0 = d1 = 0, d2 = 1, b = ell = r = 2, k = n = 1.

At height one the marked node is forced to be the root.  The coloring
  c(w,t) = w(t)
is smooth with Gamma1 = D2.  Nevertheless every genuine one-variable
candidate has both Boolean colors in its starred span.

The file also proves the local mixed-product fact responsible for
MTHJ(0,0,1,2,2,1,r) <= 1: there is a one-dimensional c-good subspace at
height one for every coloring.  Since the Ramsey numbers in the paper are
defined to be positive, this identifies the corresponding MTHJ value as 1
once the global numerical wrapper is formalized.
-/

namespace DualTree.Corollary22Audit

open VariableWord

def root : BoundedNode 2 1 :=
  ⟨[], by simp [InHomTree]⟩

theorem node_eq_root (t : BoundedNode 2 1) : t = root := by
  rcases t with ⟨s, hs⟩
  apply Subtype.ext
  dsimp [root]
  cases s with
  | nil => rfl
  | cons a s =>
      have hfalse : False := by
        simpa [InHomTree] using hs
      exact hfalse.elim

abbrev Pointed := TreeWord 2 1 Bool × BoundedNode 2 1

def color (p : Pointed) : Bool :=
  p.1 p.2

/--
Specialization of Definition 21 to D0 = D1 = empty, D2 = Gamma1 = {1}.
The whole word is fixed; the marked point is otherwise ignored.
-/
def SmoothGamma1 (c : Pointed → Bool) : Prop :=
  ∀ (w w' : TreeWord 2 1 Bool) (t t' : BoundedNode 2 1),
    w = w' → c (w,t) = c (w',t')

theorem color_is_smooth :
    SmoothGamma1 color := by
  intro w w' t t' hw
  subst w'
  rw [node_eq_root t, node_eq_root t']

def supportNodes {b n : Nat} {α : Type*}
    (f : VariableWord b n α) : List (Node b) :=
  f.support.map (fun t => t.1)

def StarredSpan (f : VariableWord 2 1 Bool) : Set Pointed :=
  {p | p.1 ∈ f.span ∧ p.2 ∈ f.support}

def Monochromatic (c : Pointed → Bool) (S : Set Pointed) : Prop :=
  ∀ ⦃x y⦄, x ∈ S → y ∈ S → c x = c y

def falseWord : TreeWord 2 1 Bool :=
  fun _ => false

def trueWord : TreeWord 2 1 Bool :=
  fun _ => true

def falsePoint : Pointed :=
  (falseWord, root)

def truePoint : Pointed :=
  (trueWord, root)

theorem root_mem_support_of_nonempty
    (f : VariableWord 2 1 Bool) (h : f.support ≠ []) :
    root ∈ f.support := by
  cases hs : f.support with
  | nil =>
      exact (h hs).elim
  | cons t ts =>
      have ht : t ∈ f.support := by simp [hs]
      have htr : t = root := node_eq_root t
      simpa [htr] using ht

theorem falseWord_mem_span
    (f : VariableWord 2 1 Bool) (hroot : root ∈ f.support) :
    falseWord ∈ f.span := by
  let v : f.Vars := ⟨root, hroot⟩
  have hv : f.word root = Sum.inr v := f.atRoot v
  change ∃ σ : f.Vars → Bool, SpanAudit.eval f.word σ = falseWord
  refine ⟨fun _ => false, ?_⟩
  funext i
  rw [node_eq_root i]
  simp [SpanAudit.eval, SpanAudit.evalSymbol, falseWord, hv]

theorem trueWord_mem_span
    (f : VariableWord 2 1 Bool) (hroot : root ∈ f.support) :
    trueWord ∈ f.span := by
  let v : f.Vars := ⟨root, hroot⟩
  have hv : f.word root = Sum.inr v := f.atRoot v
  change ∃ σ : f.Vars → Bool, SpanAudit.eval f.word σ = trueWord
  refine ⟨fun _ => true, ?_⟩
  funext i
  rw [node_eq_root i]
  simp [SpanAudit.eval, SpanAudit.evalSymbol, trueWord, hv]

theorem falsePoint_mem_starred
    (f : VariableWord 2 1 Bool) (h : f.support ≠ []) :
    falsePoint ∈ StarredSpan f := by
  have hroot := root_mem_support_of_nonempty f h
  exact ⟨falseWord_mem_span f hroot, hroot⟩

theorem truePoint_mem_starred
    (f : VariableWord 2 1 Bool) (h : f.support ≠ []) :
    truePoint ∈ StarredSpan f := by
  have hroot := root_mem_support_of_nonempty f h
  exact ⟨trueWord_mem_span f hroot, hroot⟩

theorem starred_span_not_monochromatic_of_nonempty
    (f : VariableWord 2 1 Bool) (h : f.support ≠ []) :
    ¬ Monochromatic color (StarredSpan f) := by
  intro hm
  have hc := hm
    (falsePoint_mem_starred f h)
    (truePoint_mem_starred f h)
  simp [color, falsePoint, truePoint, falseWord, trueWord] at hc

theorem support_nonempty_of_complete_one
    (f : VariableWord 2 1 Bool)
    (hcomplete :
      SkewTree.completeB SkewTree.paperAuxB 1 (supportNodes f) = true) :
    f.support ≠ [] := by
  intro hs
  have hnodes : supportNodes f = [] := by
    simp [supportNodes, hs]
  rw [hnodes] at hcomplete
  simp [SkewTree.completeB, SkewTree.skewB, SkewTree.rootedB] at hcomplete

/-- The conclusion demanded by Corollary 22 fails at height one. -/
theorem no_monochromatic_complete_candidate
    (f : VariableWord 2 1 Bool)
    (hcomplete :
      SkewTree.completeB SkewTree.paperAuxB 1 (supportNodes f) = true) :
    ¬ Monochromatic color (StarredSpan f) :=
  starred_span_not_monochromatic_of_nonempty f
    (support_nonempty_of_complete_one f hcomplete)

/-- Canonical one-variable word on the height-one tree. -/
def rootVar : {t // t ∈ [root]} :=
  ⟨root, by simp⟩

def canonical : VariableWord 2 1 Bool where
  support := [root]
  support_nodup := by simp
  word := fun _ => Sum.inr rootVar
  atRoot := by
    intro v
    have hv : v.1 = root := by simpa using v.2
    have hsub : v = rootVar := by
      apply Subtype.ext
      exact hv
    subst v
    rfl
  below := by
    intro v i h
    have hv : v.1 = root := by simpa using v.2
    rw [hv, node_eq_root i]
    exact isPrefix_refl _

theorem canonical_complete_one :
    SkewTree.completeB SkewTree.paperAuxB 1
      (supportNodes canonical) = true := by
  simpa [supportNodes, canonical] using
    (SkewTree.singleton_complete_oneB SkewTree.paperAuxB root.1)

/--
Specialization of Definition 11 for the present D2-only case.
-/
def Good {γ : Type*}
    (c : Pointed → γ) (f : VariableWord 2 1 Bool) : Prop :=
  ∀ ⦃w w' : TreeWord 2 1 Bool⦄
      ⦃t t' : BoundedNode 2 1⦄,
    w ∈ f.span → w' ∈ f.span →
    t ∈ f.support → t' ∈ f.support →
    t = t' → w t = w' t' →
    c (w,t) = c (w',t')

/--
At ambient height one the canonical one-dimensional subspace is c-good for
every coloring.  This is the local fact giving the relevant MTHJ bound 1.
-/
theorem canonical_good_for_every_coloring {γ : Type*}
    (c : Pointed → γ) :
    Good c canonical := by
  intro w w' t t' hw hw' ht ht' htt hval
  subst t'
  have htr : t = root := node_eq_root t
  subst t
  have hww' : w = w' := by
    funext i
    rw [node_eq_root i]
    exact hval
  subst w'
  rfl

end DualTree.Corollary22Audit
