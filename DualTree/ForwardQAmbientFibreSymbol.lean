import DualTree.ForwardQAmbientFibreFrame
import DualTree.ForwardQFullFrontierWord
import DualTree.ForwardQActualCoordinateWord
import DualTree.ForwardQVisibleAncestorDecoder

/-!
# Genuine ambient-fibrewise, five-case Q symbols for Lemma 27

The source-facing Frame now carries the original ambient f, its
complete support T and the explicit substitution g' = f[rho].
Therefore the printed Q map can inspect f(s), for EVERY homogeneous
tree position s, rather than attempting to decode at the frontier
cone of s itself. In particular, it reads local w_i(z) from the
ROOT of the entire f-variable fibre and uses that identical value
at every occurrence of the same source f-variable.

Cases:
  * f(s) = a in Lambda: keep a;
  * f(s) = v_t at/before the source cut: use g'(s)=g'(t),
    including retention of the distinguished cut variable;
  * f(s) = v_t AFTER the cut: use the unique corrected outside
    frontier containing the ROOT t, and recover its intrinsically
    safe canonical inverse tail z. Original letters stay original;
    auxiliary letters use the certified visible-ancestor R_i.
  * If that root has no selected frontier or its tail is outside
    the safe local domain, use the old fallback alphabet letter.

All formulas are for the original ORDINARY enlarged-alphabet
mixed-product words. There are no independent local cone variables
and no occurrence-level Hall matching.

This module proves the full f-FIBRE pointwise Q(iv) formula, not merely
its earlier projection-root special case. It also checks all cases
and fibre uniformity. The remaining obligation is to package the
resulting map as a valid old-root variable word and then starred word
on the actual corrected Q support, and verify the induced colouring
smoothness and subsequent f' construction.

The strengthened source refinement hypothesis is explicit; this
does not repair the printed order or singleton-alphabet issues.
-/

namespace DualTree.ForwardQAmbientFibreSymbol

open ForwardSourceQTree
open ForwardQAmbientFibreFrame

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α) :=
  ForwardQFullFrontierWord.Index c.core

/-- Recover the genuine chosen frontier cone from a successful
frontier selector. This is the reverse direction to the prior
selectedFrontier_eq_some_of_prefix theorem. -/
theorem selectedFrontier_some_prefix
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : BoundedNode b n)
    (i : ForwardQFullFrontierWord.Index c)
    (h : ForwardQFullFrontierWord.selectedFrontier c t = some i) :
    IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 := by
  classical
  unfold ForwardQFullFrontierWord.selectedFrontier at h
  split_ifs at h with hex
  · have hs : IsPrefix
        (ForwardOrderedProjections.frontierAt
          c.T c.cut (Classical.choose hex)).1 t.1 :=
      Classical.choose_spec hex
    have heq : Classical.choose hex = i := by
      simpa using h
    rwa [heq] at hs

/-- The paper's local two-case map Lambda' -> Lambda + old
source variables, with the input sampled at an AMBIENT f-root,
not at the potentially different original position s. -/
noncomputable def decodeAmbientRoot
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (v : c.ambient.Vars) :
    Sum α c.core.source.word.Vars :=
  match ForwardQFullFrontierWord.selectedFrontier c.core v.1 with
  | none => Sum.inl fallback
  | some i =>
      match ForwardQEnlargedConstantWords.sampledEnlarged
          c.core w fallback i v.1 with
      | Sum.inl a => Sum.inl a
      | Sum.inr j =>
          ForwardQVisibleAncestorDecoder.decodeAux
            c.core fallback i j

/-- The literal source-facing Q symbol at EVERY bounded original
ambient position s, classified by the actual f(s) FIBRE label. -/
noncomputable def fibreQSymbol
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (s : BoundedNode b n) :
    Sum α c.core.source.word.Vars :=
  match c.ambient.word s with
  | Sum.inl a => Sum.inl a
  | Sum.inr v =>
      if ForwardAux v.1.1 c.core.cut then
        c.core.source.word.word s
      else decodeAmbientRoot c fallback w v

/-- Printed clause (i): all original alphabet constants of f
survive, even at positions inside a geometric frontier cone. -/
theorem fibreQ_original_constant
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (s : BoundedNode b n)
    (a : α)
    (hs : c.ambient.word s = Sum.inl a) :
    fibreQSymbol c fallback w s = Sum.inl a := by
  simp [fibreQSymbol, hs]

/-- Printed clauses (ii),(iii): on every f-variable fibre at
or before the cut, use the existing g' symbol at that position,
which the ambient refinement proves equals g' at its ROOT. -/
theorem fibreQ_before_cut
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (s : BoundedNode b n)
    (v : c.ambient.Vars)
    (hs : c.ambient.word s = Sum.inr v)
    (hbefore : ForwardAux v.1.1 c.core.cut) :
    fibreQSymbol c fallback w s =
      c.core.source.word.word s := by
  simp [fibreQSymbol, hs, hbefore]

/-- A post-cut fibre reads its local letter or R_i auxiliary
symbol from its genuine original f-variable ROOT, never from s. -/
theorem fibreQ_after_cut
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (s : BoundedNode b n)
    (v : c.ambient.Vars)
    (hs : c.ambient.word s = Sum.inr v)
    (hafter : ¬ ForwardAux v.1.1 c.core.cut) :
    fibreQSymbol c fallback w s =
      decodeAmbientRoot c fallback w v := by
  simp [fibreQSymbol, hs, hafter]

/-- Every pair of positions in a single original ambient f
variable fibre gets the SAME decoded Q symbol: in the early
case by syntactic g' refinement, in the late case by decoding
once at the common root. This is stronger than the earlier
pointwise projected-coordinate identity. -/
theorem fibreQ_constant_on_ambient_fibre
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (v : c.ambient.Vars)
    (s t : BoundedNode b n)
    (hs : c.ambient.word s = Sum.inr v)
    (ht : c.ambient.word t = Sum.inr v) :
    fibreQSymbol c fallback w s =
      fibreQSymbol c fallback w t := by
  by_cases hbefore : ForwardAux v.1.1 c.core.cut
  · calc
      fibreQSymbol c fallback w s =
          c.core.source.word.word s :=
        fibreQ_before_cut c fallback w s v hs hbefore
      _ = c.core.source.word.word v.1 :=
        source_uniform_on_ambient_fibre c v s hs
      _ = c.core.source.word.word t :=
        (source_uniform_on_ambient_fibre c v t ht).symm
      _ = fibreQSymbol c fallback w t :=
        (fibreQ_before_cut c fallback w t v ht hbefore).symm
  · rw [fibreQ_after_cut c fallback w s v hs hbefore,
        fibreQ_after_cut c fallback w t v ht hbefore]

/-- Every old source root, including t0, still bears exactly
its own original variable after the Q construction. -/
theorem fibreQ_at_old_root
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (v : c.core.source.word.Vars) :
    fibreQSymbol c fallback w v.1 = Sum.inr v := by
  have hf :
      c.ambient.word v.1 =
        Sum.inr (ambientAtSourceRoot c v) :=
    ambient_at_source_root_symbol c v
  have hb :
      ForwardAux (ambientAtSourceRoot c v).1.1 c.core.cut := by
    simpa [ambientAtSourceRoot] using source_root_before_cut c v
  rw [fibreQ_before_cut c fallback w
    v.1 (ambientAtSourceRoot c v) hf hb]
  exact c.core.source.word.atRoot v

/-- The actual projected P_i(z) extends its minimal outside-cut
frontier and hence lies STRICTLY after that cut. -/
theorem projected_root_after_cut
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    ¬ ForwardAux
      (ForwardQActualCoordinateWord.projectLocal c.core i z).1
      c.core.cut := by
  have hfront :
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.core.T c.core.cut i).1
        (ForwardQActualCoordinateWord.projectLocal c.core i z).1 :=
    ForwardQActualCoordinateWord.projectLocal_cone c.core i z
  exact ForwardInclusiveFrontier.outside_of_prefix
    (ForwardOrderedProjections.frontierAt_spec
      c.core.T c.core.cut i).2.1 hfront

/-- The ACTUAL original ambient variable at P_i(z) recovers
exactly w_i(z) through the decoder. Both ordinary and auxiliary
letters are handled, with no local-variable Hall assumption. -/
theorem decode_ambient_projected_root
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    decodeAmbientRoot c fallback w
        (ambientAtTRoot c
          (ForwardQActualCoordinateWord.projectLocal c.core i z).1
          (ForwardQActualCoordinateWord.projectLocal c.core i z).2) =
      match w.words i z with
      | Sum.inl a => Sum.inl a
      | Sum.inr j =>
          ForwardQVisibleAncestorDecoder.decodeAux
            c.core fallback i j := by
  let p := ForwardQActualCoordinateWord.projectLocal c.core i z
  let v := ambientAtTRoot c p.1 p.2
  let u := ForwardQActualCoordinateWord.projectedBounded
    c.core c.T_bounded i z
  have hnode : v.1 = u := Subtype.ext rfl
  have hfront :
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.core.T c.core.cut i).1
        u.1 :=
    ForwardQActualCoordinateWord.projectLocal_cone c.core i z
  have hselected :
      ForwardQFullFrontierWord.selectedFrontier
        c.core v.1 = some i := by
    rw [hnode]
    exact ForwardQFullFrontierWord.selectedFrontier_eq_some_of_prefix
      c.core i u hfront
  have hletter :
      ForwardQEnlargedConstantWords.sampledEnlarged
        c.core w fallback i v.1 = w.words i z := by
    rw [hnode]
    exact ForwardQEnlargedConstantWords.sampledEnlarged_projected
      c.core w fallback c.T_bounded i z
  change (match ForwardQFullFrontierWord.selectedFrontier c.core v.1 with
    | none => Sum.inl fallback
    | some j =>
        match ForwardQEnlargedConstantWords.sampledEnlarged
          c.core w fallback j v.1 with
        | Sum.inl a => Sum.inl a
        | Sum.inr h =>
            ForwardQVisibleAncestorDecoder.decodeAux
              c.core fallback j h) = _
  rw [hselected, hletter]

/-- The FULL source-facing clause (iv) at an f-variable ROOT:
we decode actual w_i(z), never a synthetic one-cone symbol. -/
theorem fibreQ_projected_root
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    fibreQSymbol c fallback w
      (ambientAtTRoot c
        (ForwardQActualCoordinateWord.projectLocal c.core i z).1
        (ForwardQActualCoordinateWord.projectLocal c.core i z).2).1 =
      match w.words i z with
      | Sum.inl a => Sum.inl a
      | Sum.inr j =>
          ForwardQVisibleAncestorDecoder.decodeAux
            c.core fallback i j := by
  let p := ForwardQActualCoordinateWord.projectLocal c.core i z
  let v := ambientAtTRoot c p.1 p.2
  have hf : c.ambient.word v.1 = Sum.inr v :=
    ambient_at_T_root_symbol c p.1 p.2
  have hafter : ¬ ForwardAux v.1.1 c.core.cut := by
    change ¬ ForwardAux p.1 c.core.cut
    exact projected_root_after_cut c i z
  calc
    fibreQSymbol c fallback w v.1 =
      decodeAmbientRoot c fallback w v :=
      fibreQ_after_cut c fallback w v.1 v hf hafter
    _ = _ := decode_ambient_projected_root c fallback w i z

/-- The TRUE paper clause (iv) on the ENTIRE original f FIBRE:
if f(s)=v_{P_i(z)}, the value of g_w(s) equals the decoded
w_i(z), independent of the ambient position s or its cone.
This is precisely what position-based patching could not show. -/
theorem fibreQ_projected_full_fibre
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1)))
    (s : BoundedNode b n)
    (hs : c.ambient.word s =
      Sum.inr (ambientAtTRoot c
        (ForwardQActualCoordinateWord.projectLocal c.core i z).1
        (ForwardQActualCoordinateWord.projectLocal c.core i z).2)) :
    fibreQSymbol c fallback w s =
      match w.words i z with
      | Sum.inl a => Sum.inl a
      | Sum.inr j =>
          ForwardQVisibleAncestorDecoder.decodeAux
            c.core fallback i j := by
  let p := ForwardQActualCoordinateWord.projectLocal c.core i z
  let v := ambientAtTRoot c p.1 p.2
  calc
    fibreQSymbol c fallback w s =
      fibreQSymbol c fallback w v.1 :=
      fibreQ_constant_on_ambient_fibre c fallback w v s v.1
        hs (ambient_at_T_root_symbol c p.1 p.2)
    _ = _ := fibreQ_projected_root c fallback w i z

/-- Printed fallback clause: any post-cut original f-variable
whose root has no selected complete-support frontier receives
the designated original fallback letter, throughout its fibre. -/
theorem fibreQ_unprojected_no_frontier
    {b n l k m : Nat} {α : Type*}
    (c : FibreFrame b n l k m α)
    (fallback : α)
    (w : ForwardQEnlargedConstantWords.EnlargedInput c.core)
    (s : BoundedNode b n)
    (v : c.ambient.Vars)
    (hs : c.ambient.word s = Sum.inr v)
    (hafter : ¬ ForwardAux v.1.1 c.core.cut)
    (hnone :
      ForwardQFullFrontierWord.selectedFrontier c.core v.1 = none) :
    fibreQSymbol c fallback w s = Sum.inl fallback := by
  rw [fibreQ_after_cut c fallback w s v hs hafter]
  simp [decodeAmbientRoot, hnone]

end DualTree.ForwardQAmbientFibreSymbol
