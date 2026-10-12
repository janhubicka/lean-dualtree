import DualTree.ForwardQWordSymbolAssembly
import DualTree.ForwardOrderedProjections

/-!
# A corrected Q-word assembly using ALL complete-support frontier cones

The construction printed in Lemma 27 decodes a coneWord word in every
selected outside-cut complete-support FRONTIER cone, at every D0 and D2
coordinate. It does not limit symbol replacement to the smaller
cones above the chosen D2 marked points.

Earlier ForwardQThreeWayConeWordAssembly proved a conditional starred
word by patching only D2 *marked-point* cones. That theorem remains
valid, but it does not model the support of the printed word formula.

This module gives the missing full-frontier geometric/word interface.
All actual sorted outside-cut frontier cones are pairwise disjoint
throughout the ambient homogeneous tree and avoid all old variable
roots. Given root-aligned decoded coneWord words at EVERY frontier
coordinate, their global assembly is therefore a legal variable
word, and on an actual corrected starred input a legal starred word
on the same Q support. Both inside/outside symbol equalities hold.

The specific original enlarged-alphabet coneWord words, auxiliary
decoders and variable-root transport remain to be instantiated;
smoothness of c composed with this Q and Ramsey span/refinement
compatibility are not automatic.
-/

namespace DualTree.ForwardQFullFrontierWord

open ForwardSourceQTree

/-- Every member of the full forward-sorted frontier list, not
only the selected D2 markers, is a valid patch coordinate. -/
abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  Fin (ForwardSortedFrontiers.frontiers c.T c.cut).length

/-- An original source variable root lies before the last
source cut and thus cannot be in any outside-cut frontier cone. -/
theorem frontier_cone_avoids_source_root
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (v : c.source.word.Vars) :
    ¬ IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1
      v.1.1 := by
  intro hpre
  have hvInterior : v.1.1 ∈ SkewTree.interior c.source.tree :=
    StarredSignature.variable_root_in_interior c.source v
  have hvBefore : ForwardAux v.1.1 c.cut := by
    simpa [SkewTree.forwardAuxB] using c.hmax v.1.1 hvInterior
  have hfBefore : ForwardAux
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 c.cut :=
    ForwardInclusiveFrontier.forwardAux_of_prefix hpre hvBefore
  exact (ForwardOrderedProjections.frontierAt_spec
    c.T c.cut i).2.1 hfBefore

/-- Two distinct full frontier indices cannot have a common
ambient descendant, even when the descendant is not in T. -/
theorem frontier_cones_disjoint
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i j : Index c)
    (hij : i ≠ j)
    (t : Node b) :
    ¬ (IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t ∧
       IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut j).1 t) := by
  intro ⟨hi, hj⟩
  have hfi :=
    ForwardOrderedProjections.frontierAt_spec c.T c.cut i
  have hfj :=
    ForwardOrderedProjections.frontierAt_spec c.T c.cut j
  have hfront :
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 =
        (ForwardOrderedProjections.frontierAt c.T c.cut j).1 :=
    CutFrontier.frontier_unique_above c.T
      (fun u => ForwardAux u c.cut) hfi hfj hi hj
  exact hij (ForwardOrderedProjections.frontierAt_injective
    c.T c.cut (Subtype.ext hfront))

/-- The unique frontier containing a homogeneous-tree node,
if the node belongs to a selected outside-cut cone. -/
noncomputable def selectedFrontier
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : BoundedNode b n) : Option (Index c) := by
  classical
  exact if h : ∃ i : Index c,
      IsPrefix (ForwardOrderedProjections.frontierAt
        c.T c.cut i).1 t.1 then
    some (Classical.choose h)
  else none

/-- The full frontier selector is absent at EVERY source
variable root, independently of the D2 marked points. -/
theorem selectedFrontier_none_at_source_root
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (v : c.source.word.Vars) :
    selectedFrontier c v.1 = none := by
  classical
  have hn : ¬ ∃ i : Index c, IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 v.1.1 := by
    rintro ⟨i, hi⟩
    exact (frontier_cone_avoids_source_root c i v) hi
  simp [selectedFrontier, hn]

/-- A point in a frontier cone selects exactly that index,
because different frontier cones have no common descendants. -/
theorem selectedFrontier_eq_some_of_prefix
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (t : BoundedNode b n)
    (hi : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    selectedFrontier c t = some i := by
  classical
  have he : ∃ j : Index c,
      IsPrefix (ForwardOrderedProjections.frontierAt
        c.T c.cut j).1 t.1 := ⟨i, hi⟩
  have hc : IsPrefix
      (ForwardOrderedProjections.frontierAt
        c.T c.cut (Classical.choose he)).1 t.1 :=
    Classical.choose_spec he
  have hj : Classical.choose he = i := by
    by_contra hne
    exact (frontier_cones_disjoint c
      (Classical.choose he) i hne t.1) ⟨hc, hi⟩
  simp [selectedFrontier, he, hj]

/-- A point outside ALL frontier cones selects no patch
coordinate: in particular positions before the cut use the source. -/
theorem selectedFrontier_none_of_outside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (t : BoundedNode b n)
    (ht : ∀ i : Index c, ¬ IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    selectedFrontier c t = none := by
  classical
  have hn : ¬ ∃ i : Index c, IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1 := by
    rintro ⟨i, hi⟩
    exact ht i hi
  simp [selectedFrontier, hn]

/-- Patch the source symbol by one full coneWord word at EVERY
frontier index (D0 and D2). This is the source's intended
domain of symbol replacement, not just the D2 marked cones. -/
noncomputable def patchedSymbol
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (coneWord : Index c →
      BoundedNode b n → Sum α c.source.word.Vars)
    (t : BoundedNode b n) :
    Sum α c.source.word.Vars :=
  match selectedFrontier c t with
  | some i => coneWord i t
  | none => c.source.word.word t

theorem patchedSymbol_inside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (coneWord : Index c →
      BoundedNode b n → Sum α c.source.word.Vars)
    (i : Index c)
    (t : BoundedNode b n)
    (hi : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    patchedSymbol c coneWord t = coneWord i t := by
  simp [patchedSymbol, selectedFrontier_eq_some_of_prefix c i t hi]

theorem patchedSymbol_outside
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (coneWord : Index c →
      BoundedNode b n → Sum α c.source.word.Vars)
    (t : BoundedNode b n)
    (ht : ∀ i : Index c, ¬ IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    patchedSymbol c coneWord t = c.source.word.word t := by
  simp [patchedSymbol, selectedFrontier_none_of_outside c t ht]

theorem patchedSymbol_at_source_root
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (coneWord : Index c →
      BoundedNode b n → Sum α c.source.word.Vars)
    (v : c.source.word.Vars) :
    patchedSymbol c coneWord v.1 = Sum.inr v := by
  simp [patchedSymbol, selectedFrontier_none_at_source_root c v,
    c.source.word.atRoot v]

/-- Local variable occurrences must be aligned with the
actual source-root variables; otherwise the decoded global
symbol map need not be a valid tree-variable word. -/
noncomputable def toDecodedWord
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (coneWord : Index c →
      BoundedNode b n → Sum α c.source.word.Vars)
    (haligned : ∀ (i : Index c) (v : c.source.word.Vars)
      (t : BoundedNode b n),
      coneWord i t = Sum.inr v → IsPrefix v.1.1 t.1) :
    ForwardQWordSymbolAssembly.DecodedWord c := {
  symbol := patchedSymbol c coneWord
  atRoot := patchedSymbol_at_source_root c coneWord
  below := by
    intro v t h
    cases hsel : selectedFrontier c t with
    | none =>
        have hs : c.source.word.word t = Sum.inr v := by
          simpa [patchedSymbol, hsel] using h
        exact c.source.word.below v t hs
    | some i =>
        have hs : coneWord i t = Sum.inr v := by
          simpa [patchedSymbol, hsel] using h
        exact haligned i v t hs
}

/-- The full-frontier patched map is an actual valid variable
word, with precisely the old source root support. -/
noncomputable def toVariableWord
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (coneWord : Index c →
      BoundedNode b n → Sum α c.source.word.Vars)
    (haligned : ∀ (i : Index c) (v : c.source.word.Vars)
      (t : BoundedNode b n),
      coneWord i t = Sum.inr v → IsPrefix v.1.1 t.1) :
    DualTree.VariableWord b n α :=
  (toDecodedWord c coneWord haligned).toVariableWord

/-- A full-frontier patched word is a legal starred word on
the ACTUAL corrected Q support, provided the selected input
satisfies the canonical corrected Wstar condition. -/
noncomputable def onActualStarredQ
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (coneWord : Index c →
      BoundedNode b n → Sum α c.source.word.Vars)
    (haligned : ∀ (i : Index c) (v : c.source.word.Vars)
      (t : BoundedNode b n),
      coneWord i t = Sum.inr v → IsPrefix v.1.1 t.1) :
    StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) :=
  (toDecodedWord c coneWord haligned).onCorrectedQ hb c x.1
    ((ForwardQActualStarredSpace.isStarred_iff_bullet_lengths_ordered
      c x.1).1 x.2) hTbound

theorem onActualStarredQ_tree
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (coneWord : Index c →
      BoundedNode b n → Sum α c.source.word.Vars)
    (haligned : ∀ (i : Index c) (v : c.source.word.Vars)
      (t : BoundedNode b n),
      coneWord i t = Sum.inr v → IsPrefix v.1.1 t.1) :
    (onActualStarredQ hb c x hTbound coneWord haligned).tree =
      (nodes c x.1).toList := rfl

theorem onActualStarredQ_symbol_inside
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (coneWord : Index c →
      BoundedNode b n → Sum α c.source.word.Vars)
    (haligned : ∀ (i : Index c) (v : c.source.word.Vars)
      (t : BoundedNode b n),
      coneWord i t = Sum.inr v → IsPrefix v.1.1 t.1)
    (i : Index c)
    (t : BoundedNode b n)
    (hi : IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    (onActualStarredQ hb c x hTbound coneWord haligned).word.word t =
      coneWord i t := by
  change patchedSymbol c coneWord t = coneWord i t
  exact patchedSymbol_inside c coneWord i t hi

theorem onActualStarredQ_symbol_outside
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (coneWord : Index c →
      BoundedNode b n → Sum α c.source.word.Vars)
    (haligned : ∀ (i : Index c) (v : c.source.word.Vars)
      (t : BoundedNode b n),
      coneWord i t = Sum.inr v → IsPrefix v.1.1 t.1)
    (t : BoundedNode b n)
    (ht : ∀ i : Index c, ¬ IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1 t.1) :
    (onActualStarredQ hb c x hTbound coneWord haligned).word.word t =
      c.source.word.word t := by
  change patchedSymbol c coneWord t = c.source.word.word t
  exact patchedSymbol_outside c coneWord t ht

/-- The complete-frontier decoded word keeps exactly the source
variable-root list, rather than silently adding one variable
for each frontier or for each marker. -/
theorem toVariableWord_support
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (coneWord : Index c →
      BoundedNode b n → Sum α c.source.word.Vars)
    (haligned : ∀ (i : Index c) (v : c.source.word.Vars)
      (t : BoundedNode b n),
      coneWord i t = Sum.inr v → IsPrefix v.1.1 t.1) :
    (toVariableWord c coneWord haligned).support =
      c.source.word.support := rfl

/-- For fixed coneWord decoded frontier words, the actual output
word is independent of the selected D₂ marked-point array.
Only the output SUPPORT tree depends on that array. This
distinction is needed for Definition 21's Gamma₁ coordinates,
whose points are allowed to move. -/
theorem onActualStarredQ_word_eq_for_fixed_local
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x y : ForwardQActualStarredSpace.StarredInput c)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (coneWord : Index c →
      BoundedNode b n → Sum α c.source.word.Vars)
    (haligned : ∀ (i : Index c) (v : c.source.word.Vars)
      (t : BoundedNode b n),
      coneWord i t = Sum.inr v → IsPrefix v.1.1 t.1) :
    (onActualStarredQ hb c x hTbound coneWord haligned).word.word =
      (onActualStarredQ hb c y hTbound coneWord haligned).word.word := rfl

end DualTree.ForwardQFullFrontierWord
