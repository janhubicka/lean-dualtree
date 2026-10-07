import DualTree.SignatureBoundary
import DualTree.KVariableWord

/-!
# Starred tree-variable words and the partial signature skeleton

This module models Definition 23 on the finite tree types of Section 3:
a semi-complete skew tree S, a variable word g with the same interior roots,
and the designated number l of interior vertices. In particular g's support
must itself be a skew tree when l > 0, as required by W_v,l^times.

The signature of Definition 26 contains the interior of S and boundary
points obtained from certain leaves. Its construction is deliberately
conditional on the existence of the prescribed ambient path minima.
The remaining task is to derive that condition from the full
semi-complete/skew hypotheses, rather than silently discard undefined
boundary points.
-/

namespace DualTree.StarredSignature

/-- The source-facing objects (S,g) of W^*_{v,l}. -/
structure StarredWord (b n l : Nat) (α : Type*)
    (aux : Node b → Node b → Bool) where
  tree : List (Node b)
  tree_bounded : ∀ t, t ∈ tree → InHomTree n t
  semi_complete : SkewTree.semiCompleteB aux tree = true
  word : VariableWord b n α
  interior_card : (SkewTree.interior tree).length = l
  support_eq_interior :
    ∀ t : Node b,
      t ∈ word.supportNodes ↔ t ∈ SkewTree.interior tree
  support_skew : 0 < l →
    SkewTree.skewB aux word.supportNodes = true

/-- Every support root in a starred object is an interior vertex of S. -/
theorem variable_root_in_interior
    {b n l : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    (O : StarredWord b n l α aux)
    (v : O.word.Vars) :
    v.1.1 ∈ SkewTree.interior O.tree := by
  apply (O.support_eq_interior v.1.1).1
  change v.1.1 ∈ O.word.support.map (fun t => t.1)
  exact List.mem_map.mpr ⟨v.1, v.2, rfl⟩

/-- Conversely, every interior vertex labels a variable occurring at its root. -/
theorem variable_at_interior
    {b n l : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    (O : StarredWord b n l α aux)
    (s : Node b)
    (hs : s ∈ SkewTree.interior O.tree) :
    ∃ v : O.word.Vars,
      v.1.1 = s ∧ O.word.word v.1 = Sum.inr v := by
  have hs' : s ∈ O.word.supportNodes :=
    (O.support_eq_interior s).2 hs
  change s ∈ O.word.support.map (fun t => t.1) at hs'
  rcases List.mem_map.mp hs' with ⟨t, ht, heq⟩
  let v : O.word.Vars := ⟨t, ht⟩
  exact ⟨v, heq, O.word.atRoot v⟩

/-- Leaves selected by the second term of Definition 26's signature tree. -/
noncomputable def exceptionalLeaves
    {b n l : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    (O : StarredWord b n l α aux)
    (cut : Node b) : List (Node b) := by
  classical
  exact O.tree.filter (fun t =>
    decide (t ∉ SkewTree.interior O.tree ∧ ¬ IsPrefix cut t))

theorem exceptionalLeaves_spec
    {b n l : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    (O : StarredWord b n l α aux)
    (cut t : Node b)
    (ht : t ∈ exceptionalLeaves O cut) :
    t ∈ O.tree ∧ t ∉ SkewTree.interior O.tree ∧
      ¬ IsPrefix cut t := by
  classical
  simpa [exceptionalLeaves, and_assoc, and_left_comm, and_comm] using ht

/--
Conditional signature tree S': all interior vertices plus the first
non-early prefix of each leaf not below the cut. The extra hypothesis
guarantees that all the minima in Definition 26 actually exist.
-/
noncomputable def signatureTree
    {b n l : Nat} {α : Type*}
    (O : StarredWord b n l α (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t) :
    List (Node b) := by
  classical
  let boundary := (exceptionalLeaves O cut).attach.map
    (fun t => SignatureBoundary.firstBoundary cut t.1
      (hout t.1 t.2))
  exact (SkewTree.interior O.tree ++ boundary).eraseDups

/-- No interior vertex disappears when the signature skeleton is formed. -/
theorem interior_mem_signatureTree
    {b n l : Nat} {α : Type*}
    (O : StarredWord b n l α (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hout : ∀ t, t ∈ exceptionalLeaves O cut →
      ¬ SignatureBoundary.BeforeCut cut t)
    {s : Node b}
    (hs : s ∈ SkewTree.interior O.tree) :
    s ∈ signatureTree O cut hout := by
  classical
  unfold signatureTree
  simp [hs]

/-- Definition 26's restricted word, with variables identified by their roots. -/
def prefixWord
    {b n : Nat} {α : Type*}
    (f : VariableWord b n α)
    (cut : BoundedNode b n) :
    {s : BoundedNode b n //
      SignatureBoundary.BeforeCut cut.1 s.1} →
        Sum α (BoundedNode b n) :=
  fun s => CutPreservation.underlyingSymbol f s.1

/--
The prefix-word component of the signature is invariant under a syntactic
refinement retaining all variable roots up to the cut.
-/
theorem prefixWord_eq_of_syntactic_refinement
    {b n : Nat} {α : Type*}
    (f g : VariableWord b n α)
    (ρ : f.Vars → Sum α g.Vars)
    (hword : g.word = SpanAudit.substitute f.word ρ)
    (cut : BoundedNode b n)
    (hkeep : ∀ r, r ∈ f.support →
      PaperAux r.1 cut.1 → r ∈ g.support) :
    prefixWord g cut = prefixWord f cut := by
  funext s
  exact CutPreservation.paperCut_preserved_of_syntactic_refinement
    f g ρ hword cut hkeep s.1 s.2.1

end DualTree.StarredSignature
