import DualTree.ForwardQEnlargedConstantWords

/-!
# Supply the missing original ambient word f to Lemma 27's Q frame

The printed Q(s) inspects the symbol of the original ambient
complete-support VARIABLE WORD f at the actual homogeneous-tree
position s. The existing corrected Frame carries only the starred
word (S,g') and the complete support T; neither determines the
fibre partition of the ambient positions induced by f.

A strengthened frame therefore records:
  * an actual ambient variable word f;
  * that ALL of its roots, and no others, are precisely T;
  * the n-bound on T (implied by an original ambient f witness);
  * the actual substitution rho proving g' is a refinement of f.

This is no gratuitous change to the original lemma: f and
[S,g'] <= f are present as hypotheses there. Using the
witness rho instead of a mere assertion of evaluated-span
inclusion avoids a false dependency on a two-letter alphabet:
over a singleton alphabet span containment does not imply
syntactic substitution.

We prove that old source roots are actual ambient f roots,
rho fixes those variables at their roots, and g' is UNIFORM
on each original f fibre. These facts let the next stage
define g_w by the source's five genuine f-fibre cases,
not by the ambient position's frontier cone.

This module does not yet construct the full corrected g_w,
the simple-colouring pullback, or the final f' refinement.
-/

namespace DualTree.ForwardQAmbientFibreFrame

open ForwardSourceQTree

/-- Genuine source-facing setting of printed Lemma 27:
an ambient complete-support variable word with exactly T roots,
and an explicit uniform syntactic refinement into g'. -/
structure FibreFrame
    (b n l k m : Nat) (α : Type*) where
  core : Frame b n l k m α
  ambient : DualTree.VariableWord b n α
  ambient_support_T :
    ∀ t : BoundedNode b n,
      t ∈ ambient.support ↔ t.1 ∈ core.T
  T_bounded : ∀ t : Node b, t ∈ core.T → InHomTree n t
  substitution : ambient.Vars → Sum α core.source.word.Vars
  source_substitution :
    core.source.word.word =
      SpanAudit.substitute ambient.word substitution

/-- Every root of g' belongs to its T support, hence to
the ACTUAL ambient variable-word support, not merely a
freely guessed node in the original homogeneous tree. -/
theorem source_root_in_ambient
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (v : c.core.source.word.Vars) :
    v.1 ∈ c.ambient.support := by
  have hint :
      v.1.1 ∈ SkewTree.interior c.core.source.tree :=
    StarredSignature.variable_root_in_interior c.core.source v
  have htree : v.1.1 ∈ c.core.source.tree := by
    unfold SkewTree.interior at hint
    exact (List.mem_filter.mp hint).1
  exact (c.ambient_support_T v.1).2
    (c.core.hST v.1.1 htree)

/-- An actual ambient f variable at each old source-variable
root; no root name is synthesized outside the original support. -/
def ambientAtSourceRoot
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (v : c.core.source.word.Vars) :
    c.ambient.Vars :=
  ⟨v.1, source_root_in_ambient c v⟩

theorem ambientAtSourceRoot_node
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (v : c.core.source.word.Vars) :
    (ambientAtSourceRoot c v).1 = v.1 :=
  rfl

/-- Original ambient f actually emits its OWN variable at
each preserved source root, as required by the printed case
(iii) for the cut and the old-root cases generally. -/
theorem ambient_at_source_root_symbol
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (v : c.core.source.word.Vars) :
    c.ambient.word v.1 =
      Sum.inr (ambientAtSourceRoot c v) :=
  c.ambient.atRoot (ambientAtSourceRoot c v)

/-- The original f variable at any old source root lies at
or before the corrected forward cut. -/
theorem source_root_before_cut
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (v : c.core.source.word.Vars) :
    ForwardAux v.1.1 c.core.cut := by
  have hinterior :
      v.1.1 ∈ SkewTree.interior c.core.source.tree :=
    StarredSignature.variable_root_in_interior c.core.source v
  simpa [SkewTree.forwardAuxB] using
    c.core.hmax v.1.1 hinterior

/-- The ambient f support is exactly T in the converse direction,
including its concrete bounded witness at each T node. -/
noncomputable def ambientAtTRoot
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (r : Node b)
    (hr : r ∈ c.core.T) :
    c.ambient.Vars :=
  ⟨⟨r, c.T_bounded r hr⟩,
    (c.ambient_support_T ⟨r, c.T_bounded r hr⟩).2 hr⟩

theorem ambientAtTRoot_node
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (r : Node b) (hr : r ∈ c.core.T) :
    (ambientAtTRoot c r hr).1.1 = r :=
  rfl

theorem ambient_at_T_root_symbol
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (r : Node b) (hr : r ∈ c.core.T) :
    c.ambient.word (ambientAtTRoot c r hr).1 =
      Sum.inr (ambientAtTRoot c r hr) :=
  c.ambient.atRoot (ambientAtTRoot c r hr)

/-- The refinement does not alter ANY alphabet constant of
the original ambient f, including before, at or after cut. -/
theorem source_constant_of_ambient_constant
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (t : BoundedNode b n)
    (a : α)
    (hf : c.ambient.word t = Sum.inl a) :
    c.core.source.word.word t = Sum.inl a := by
  rw [c.source_substitution]
  simp [SpanAudit.substitute, hf]

/-- g' has exactly the same substituted symbol at all positions
of a GIVEN original f-variable fibre. This is crucial: using
g'(t) at an arbitrary ambient position equals the printed
g'(root(f(t))) only AFTER this compatibility is established. -/
theorem source_uniform_on_ambient_fibre
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (v : c.ambient.Vars)
    (s : BoundedNode b n)
    (hs : c.ambient.word s = Sum.inr v) :
    c.core.source.word.word s =
      c.core.source.word.word v.1 := by
  rw [c.source_substitution]
  simp [SpanAudit.substitute, hs, c.ambient.atRoot v]

/-- At an old g' variable root, the actual substitution
rho returns that IDENTICAL old variable (no accidental
renaming of the preserved cut or interior roots). -/
theorem source_substitution_fixes_old_root
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (v : c.core.source.word.Vars) :
    c.substitution (ambientAtSourceRoot c v) =
      Sum.inr v := by
  have hroot :
      c.core.source.word.word v.1 = Sum.inr v :=
    c.core.source.word.atRoot v
  rw [c.source_substitution] at hroot
  simpa [SpanAudit.substitute,
    ambient_at_source_root_symbol c v] using hroot

/-- The old source variable v stays v throughout its
WHOLE original f fibre, as the printed proof needs for its
initial-segment and cut cases. -/
theorem old_root_fibre_is_retained
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (v : c.core.source.word.Vars)
    (s : BoundedNode b n)
    (hs : c.ambient.word s =
      Sum.inr (ambientAtSourceRoot c v)) :
    c.core.source.word.word s = Sum.inr v := by
  calc
    c.core.source.word.word s =
      c.core.source.word.word (ambientAtSourceRoot c v).1 :=
      source_uniform_on_ambient_fibre c
        (ambientAtSourceRoot c v) s hs
    _ = Sum.inr v := by
      simpa [ambientAtSourceRoot] using
        c.core.source.word.atRoot v

end DualTree.ForwardQAmbientFibreFrame
