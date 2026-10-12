import DualTree.ForwardQFullFrontierThreeWay
import DualTree.ForwardUniformConeDomains
import DualTree.ForwardQVisibleAncestorDecoder

/-!
# Read an ACTUAL mixed-product coordinate word on projected Q positions

The generic corrected full-frontier Q-word assembly had accepted a
pre-decoded local symbol map at every sorted complete-support frontier,
but had not yet read the actual coordinate WORDS x.words i of the
mixed-product element x : Input c.

This module supplies a concrete interpolation on the ambient tree:
when t belongs to the complete support T, take the genuine canonical
inverse address of t, remove the inverse address of frontier f_i,
and, if the resulting local tail lies in the uniformly safe
b^{< k-(m+1)} domain, read x.words i at that tail.
Else use a fallback original alphabet letter.

At the ACTUAL forward-complete projection P_i(z) of every safe local
tail z, the inverse-address identity makes the recovered local tail
literally z. Thus the interpolated local symbol equals x.words i z,
on all sorted D0 and D2 frontier indices.

The all-frontier three-constructor decoder can now be instantiated
with those ACTUAL coordinate letters (original-letter branch only),
yielding a legal starred Q word whose symbol at each P_i(z) is
exactly that input coordinate letter. Old source roots are retained.

This is a genuine source-facing glue lemma, not the complete
paper-specific mixed cone word g_w: auxiliary letters, local-variable
word substitution, the simplicity-to-smoothness comparison, and
the promised Ramsey span/iteration remain separate obligations.
-/

namespace DualTree.ForwardQActualCoordinateWord

open ForwardSourceQTree

abbrev Index
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  ForwardQFullFrontierWord.Index c

/-- The literal forward-complete projection P_i(z) for EVERY
sorted frontier index i, not just the D2 bullet subtype. -/
noncomputable def projectLocal
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    {t : Node b // t ∈ c.T} :=
  ForwardUniformConeDomains.projectCommon
    c.T c.hcomplete c.hnon c.cut c.hcutT c.hm
    (ForwardOrderedProjections.frontierAt c.T c.cut i)
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut i) z

theorem projectLocal_cone
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    IsPrefix
      (ForwardOrderedProjections.frontierAt c.T c.cut i).1
      (projectLocal c i z).1 :=
  ForwardUniformConeDomains.projectCommon_cone
    c.T c.hcomplete c.hnon c.cut c.hcutT c.hm
    (ForwardOrderedProjections.frontierAt c.T c.cut i)
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut i) z

/-- The actual inverse of P_i(z) is inverse(f_i) ++ z. -/
theorem projectLocal_inverse
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    (ForwardCompleteBijection.inverseAddress c.T c.hcomplete c.hnon
      (projectLocal c i z)).1 =
      (ForwardCompleteBijection.inverseAddress c.T c.hcomplete c.hnon
        (ForwardOrderedProjections.frontierAt c.T c.cut i)).1 ++ z.1 :=
  ForwardUniformConeDomains.projectCommon_inverse
    c.T c.hcomplete c.hnon c.cut c.hcutT c.hm
    (ForwardOrderedProjections.frontierAt c.T c.cut i)
    (ForwardOrderedProjections.frontierAt_spec c.T c.cut i) z

/-- Recover the local address at an arbitrary actual T support
node by dropping the canonical address of frontier f_i. -/
noncomputable def tailOfTNode
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (u : {t : Node b // t ∈ c.T}) : Node b :=
  (ForwardCompleteBijection.inverseAddress c.T c.hcomplete c.hnon
    u).1.drop
    (ForwardCompleteBijection.inverseAddress c.T c.hcomplete c.hnon
      (ForwardOrderedProjections.frontierAt c.T c.cut i)).1.length

/-- At the genuine support-valued projection, the inverse address
recovers precisely the ORIGINAL local tail, not an unrelated
chosen element of the same frontier cone. -/
theorem tailOfTNode_projectLocal
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    tailOfTNode c i (projectLocal c i z) = z.1 := by
  have hinv := projectLocal_inverse c i z
  unfold tailOfTNode
  rw [hinv]
  simp

/-- Interpolate ACTUAL coordinate word letters at every ambient
position. Positions outside T, or tails outside the intrinsically
safe common cone height, use the prescribed original fallback. -/
noncomputable def sampledLetter
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (fallback : α)
    (i : Index c)
    (t : BoundedNode b n) : α := by
  classical
  exact if ht : t.1 ∈ c.T then
    let u : {v : Node b // v ∈ c.T} := ⟨t.1, ht⟩
    if hz : InHomTree (k - (m + 1)) (tailOfTNode c i u) then
      x.words i ⟨tailOfTNode c i u, hz⟩
    else fallback
  else fallback

/-- The actual support projection is n-bounded under the
same explicit ambient-T boundedness hypothesis as the
checked full Q starred-word constructor. -/
noncomputable def projectedBounded
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    BoundedNode b n :=
  ⟨(projectLocal c i z).1,
    hTbound _ (projectLocal c i z).2⟩

/-- At the ACTUAL corrected P_i(z), the interpolated letter is
precisely the mixed-product input word x_i(z). This is the
missing source-facing coordinate identity for all D0/D2 cones. -/
theorem sampledLetter_projected
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    sampledLetter c x fallback i
      (projectedBounded c hTbound i z) =
      x.words i z := by
  classical
  have htail := tailOfTNode_projectLocal c i z
  simp [sampledLetter, projectedBounded,
    (projectLocal c i z).2, htail, z.2]

/-- Embed those genuine coordinate letters in the ORIGINAL-letter
constructor of the typed raw word. The auxiliary and genuine
variable constructors are deliberately absent for now. -/
noncomputable def rawCoordinateLetters
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (fallback : α) :
    Index c → BoundedNode b n →
      Sum (Sum α (Fin (m + 1))) PEmpty :=
  fun i t => Sum.inl (Sum.inl (sampledLetter c x fallback i t))

/-- The actual local raw word at P_i(z) reproduces x_i(z)
under the typed original-letter constructor. -/
theorem rawCoordinateLetters_projected
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    rawCoordinateLetters c x fallback i
      (projectedBounded c hTbound i z) =
        Sum.inl (Sum.inl (x.words i z)) := by
  simp [rawCoordinateLetters,
    sampledLetter_projected c x fallback hTbound i z]

/-- A completely typed full-frontier three-way datum reading
actual input coordinate letters, with no local cone variables.
The concrete visible-ancestor auxiliary decoder is available
but unused by these raw constant-letter symbols. -/
noncomputable def coordinateConeData
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (fallback : α) :
    ForwardQFullFrontierThreeWay.ConeData c (Fin (m + 1)) PEmpty where
  raw := rawCoordinateLetters c x fallback
  decodeAux := ForwardQVisibleAncestorDecoder.decodeAux c fallback
  coneRoot := fun _ z => nomatch z
  auxiliaryAligned := by
    intro i t a v hraw _
    simp [rawCoordinateLetters] at hraw
  coneAligned := by
    intro i t z _
    cases z

/-- The projected word has the verified corrected Q support,
while the original source variable roots are unchanged. -/
theorem coordinateConeData_Q_tree
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t) :
    ((coordinateConeData c x.1 fallback).onActualStarredQ
      hb c x hTbound).tree = (nodes c x.1).toList :=
  (coordinateConeData c x.1 fallback).onActualStarredQ_tree
    hb c x hTbound

/-- The source-facing output word actually reads the selected
mixed-product local coordinate word at every certified P_i(z).
This applies to all forward-sorted D0 and D2 coordinates. -/
theorem coordinateConeData_Q_symbol_projected
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : ForwardQActualStarredSpace.StarredInput c)
    (fallback : α)
    (hTbound : ∀ t : Node b, t ∈ c.T → InHomTree n t)
    (i : Index c)
    (z : BoundedNode b (k - (m + 1))) :
    ((coordinateConeData c x.1 fallback).onActualStarredQ
      hb c x hTbound).word.word
        (projectedBounded c hTbound i z) =
      Sum.inl (x.1.words i z) := by
  have hcone :
      IsPrefix
        (ForwardOrderedProjections.frontierAt c.T c.cut i).1
        (projectedBounded c hTbound i z).1 :=
    projectLocal_cone c i z
  have hsymbol :=
    (coordinateConeData c x.1 fallback).symbol_inside
      hb c x hTbound i
      (projectedBounded c hTbound i z) hcone
  calc
    ((coordinateConeData c x.1 fallback).onActualStarredQ
      hb c x hTbound).word.word
        (projectedBounded c hTbound i z) =
        (coordinateConeData c x.1 fallback).localSymbol i
          (projectedBounded c hTbound i z) := hsymbol
    _ = Sum.inl
          (sampledLetter c x.1 fallback i
            (projectedBounded c hTbound i z)) := rfl
    _ = Sum.inl (x.1.words i z) :=
      congrArg Sum.inl
        (sampledLetter_projected c x.1 fallback hTbound i z)

end DualTree.ForwardQActualCoordinateWord
