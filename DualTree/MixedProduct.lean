import DualTree.KVariableWord
import DualTree.VectorSkew

/-!
# Mixed products of tree-indexed words

This file formalizes the source-facing data of Section 4.1.

The paper uses a partition D = (D0,D1,D2) of the coordinate set.  We encode
the same information by a coordinate-kind function:
* plain  = D0, carrying only a word;
* up     = D1, carrying a word and a leaf at ambient level n;
* bullet = D2, carrying a word and a node below level n.

Variable mixed products consist of a vector complete skew family of variable
words, together with the last-level sets required in the D1 coordinates.
-/

namespace DualTree.MixedProduct

inductive CoordKind where
  | plain
  | up
  | bullet
  deriving DecidableEq, Repr

abbrev UpIndex {d : Nat} (kind : Fin d → CoordKind) :=
  {i : Fin d // kind i = CoordKind.up}

abbrev BulletIndex {d : Nat} (kind : Fin d → CoordKind) :=
  {i : Fin d // kind i = CoordKind.bullet}

/-- A node on the exact ambient level n. -/
abbrev LeafNode (b n : Nat) :=
  {s : Node b // s.length = n}

/--
An element of the mixed product W^D(b,n,alpha), written in the triple form
used throughout Section 4.
-/
structure Element
    (b n d : Nat) (α : Type*)
    (kind : Fin d → CoordKind) where
  words : Fin d → TreeWord b n α
  upPoint : UpIndex kind → LeafNode b n
  bulletPoint : BulletIndex kind → BoundedNode b n

/--
A variable word of the plain product W^d: every coordinate has the same
intrinsic dimension k, and the supports form a vector k-complete skew tree.
-/
structure VectorVariableWord
    (b n d k : Nat) (α : Type*)
    (aux : Node b → Node b → Bool) where
  components : Fin d → KVariableWord b n k α aux
  vector_complete :
    VectorSkew.vectorCompleteB aux k
      (fun i => (components i).toVariableWord.supportNodes) = true

namespace VectorVariableWord

def span
    {b n d k : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    (f : VectorVariableWord b n d k α aux) :
    Set (Fin d → TreeWord b n α) :=
  {w | ∀ i, w i ∈ (f.components i).span}

end VectorVariableWord

/-- Support roots followed by chosen ambient leaves in one D1 coordinate. -/
def extendedSupport
    {b n k : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    (f : KVariableWord b n k α aux)
    (X : List (LeafNode b n)) : List (Node b) :=
  f.toVariableWord.supportNodes ++ X.map Subtype.val

/--
A variable word of the mixed product W^D.

For each D1/up coordinate, X has exactly b^k leaves and adjoining those leaves
to the variable support is skew, matching the definition of W^up_v.
-/
structure VariableWord
    (b n d k : Nat) (α : Type*)
    (aux : Node b → Node b → Bool)
    (kind : Fin d → CoordKind) where
  vector : VectorVariableWord b n d k α aux
  upLeaves : UpIndex kind → List (LeafNode b n)
  upLeaves_nodup : ∀ i, (upLeaves i).Nodup
  upLeaves_card : ∀ i, (upLeaves i).length = b ^ k
  up_support_skew :
    ∀ i, SkewTree.skewB aux
      (extendedSupport (vector.components i.1) (upLeaves i)) = true

namespace VariableWord

/--
Combinatorial span of a mixed-product variable word.

The word coordinates range independently over the component spans; D1 points
range over the selected last-level sets; D2 points range over the corresponding
variable supports.
-/
def span
    {b n d k : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    (f : VariableWord b n d k α aux kind) :
    Set (Element b n d α kind) :=
  {x |
    (∀ i, x.words i ∈ (f.vector.components i).span) ∧
    (∀ i, x.upPoint i ∈ f.upLeaves i) ∧
    (∀ i, x.bulletPoint i ∈ (f.vector.components i.1).support)}

theorem word_mem_of_mem_span
    {b n d k : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    {f : VariableWord b n d k α aux kind}
    {x : Element b n d α kind}
    (hx : x ∈ f.span) (i : Fin d) :
    x.words i ∈ (f.vector.components i).span :=
  hx.1 i

theorem upPoint_mem_of_mem_span
    {b n d k : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    {f : VariableWord b n d k α aux kind}
    {x : Element b n d α kind}
    (hx : x ∈ f.span) (i : UpIndex kind) :
    x.upPoint i ∈ f.upLeaves i :=
  hx.2.1 i

theorem bulletPoint_mem_support_of_mem_span
    {b n d k : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    {kind : Fin d → CoordKind}
    {f : VariableWord b n d k α aux kind}
    {x : Element b n d α kind}
    (hx : x ∈ f.span) (i : BulletIndex kind) :
    x.bulletPoint i ∈ (f.vector.components i.1).support :=
  hx.2.2 i

end VariableWord

end DualTree.MixedProduct
