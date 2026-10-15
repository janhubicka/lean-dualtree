import DualTree.ForwardQModelVertexEquiv
import DualTree.ForwardSourceHeapInitial

/-!
# Prefix reflection for canonical addresses of semi-complete skew sources

The actual semi-complete forward-skew source has a bijective
canonical direction walk from admissible words to support
vertices. Its prefix monotonicity is already checked.

The reverse direction needs a separate argument. If realized
u prefixes realized v, follow the unique directional support
successors from realized u to realized v. The generic source
reachability theorem gives an admissible tail w, so u++w is
an admissible address realizing exactly v. Injectivity of the
whole rooted admissible walk forces u++w=v.

Thus the genuine canonical source address map preserves AND
reflects ambient prefix order; the same holds for strict prefixes.
We then specialize it to the exactly first-l homogeneous interior
addresses using the verified full heap initiality. This is the
interior/interior part of the corrected model-to-Q canonical tree
isomorphism, and requires no false printed reverse-lex order claim.

The remaining boundary extension must be proved independently,
as must the canonical selector on arbitrary starred outputs.
-/

namespace DualTree.ForwardSourceAddressPrefixIso

open ForwardSourceQTree
open ForwardSourceCanonicalAddresses
open ForwardSourceHeapInitial
open ForwardQModelVertexEquiv
open ForwardModelBoundaryHeap
open ForwardSourceAddressOrder
open ForwardSourceInteriorFirstL

/-- The actual semi-complete source walk preserves every initial
segment relation between two genuine admissible root addresses. -/
theorem sourceAddress_prefix_mono
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : SourceAddress c)
    (huv : IsPrefix u.1 v.1) :
    IsPrefix (realize c u).1 (realize c v).1 := by
  change IsPrefix
    (CanonicalSupportWalk.walk c.source.tree
      (ForwardQRooted.sourceRoot c) u.1)
    (CanonicalSupportWalk.walk c.source.tree
      (ForwardQRooted.sourceRoot c) v.1)
  exact CanonicalSupportWalk.walk_prefix
    c.source.tree (ForwardQRooted.sourceRoot c) huv

/-- In the actual semi-complete source, ambient prefix inclusion
of realized vertices REFLECTS prefix inclusion of their
unique admissible direction addresses. The proof is a genuine
reconstruction of the tail, not a cardinality argument. -/
theorem sourceAddress_prefix_reflect
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : SourceAddress c)
    (himage : IsPrefix (realize c u).1 (realize c v).1) :
    IsPrefix u.1 v.1 := by
  obtain ⟨tail, htailAdmissible, htailWalk⟩ :=
    source_walk_address_of_prefix c
      (realize c u).1 (realize c v).1
      (realize c u).2 (realize c v).2 himage
  have hconcat :
      CanonicalSupportWalk.Admissible c.source.tree
        (ForwardQRooted.sourceRoot c) (u.1 ++ tail) :=
    admissible_append c.source.tree u.1
      (ForwardQRooted.sourceRoot c) tail u.2 htailAdmissible
  have hwalkEq :
      CanonicalSupportWalk.walk c.source.tree
        (ForwardQRooted.sourceRoot c) (u.1 ++ tail) =
      CanonicalSupportWalk.walk c.source.tree
        (ForwardQRooted.sourceRoot c) v.1 := by
    rw [CanonicalSupportWalk.walk_append]
    change CanonicalSupportWalk.walk c.source.tree
      (realize c u).1 tail = (realize c v).1
    exact htailWalk
  have hsource : u.1 ++ tail = v.1 :=
    CanonicalSupportInjective.walk_injective_of_admissible
      c.source.tree (u.1 ++ tail)
      (ForwardQRooted.sourceRoot c) v.1
      hconcat v.2 hwalkEq
  exact ⟨tail, hsource.symm⟩

/-- The genuine rooted source is canonically isomorphic as
a PREFIX tree to its subtype of admissible directional words.
This is stronger than bijectivity alone. -/
theorem sourceAddress_prefix_iff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : SourceAddress c) :
    IsPrefix u.1 v.1 ↔
      IsPrefix (realize c u).1 (realize c v).1 :=
  ⟨sourceAddress_prefix_mono c u v,
   sourceAddress_prefix_reflect c u v⟩

/-- The canonical source address walk also preserves and
reflects STRICT prefixes, even along stretched ambient support
edges and with unequal source terminal heights. -/
theorem sourceAddress_strictPrefix_iff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : SourceAddress c) :
    IsStrictPrefix u.1 v.1 ↔
      IsStrictPrefix (realize c u).1 (realize c v).1 := by
  constructor
  · rintro ⟨hp, hne⟩
    refine ⟨(sourceAddress_prefix_iff c u v).1 hp, ?_⟩
    intro heq
    have huv : u = v :=
      realize_injective c (Subtype.ext heq)
    exact hne (congrArg (fun z : SourceAddress c => z.1) huv)
  · rintro ⟨hp, hne⟩
    refine ⟨(sourceAddress_prefix_iff c u v).2 hp, ?_⟩
    intro heq
    have huv : u = v := Subtype.ext heq
    subst v
    exact hne rfl

/-- The canonically realized original source interior
vertex at a first-l model address is the actual rooted
directional support walk at that address. -/
theorem modelInteriorSourceEquiv_value
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (a : ModelInteriorVertex c) :
    ((modelInteriorSourceEquiv hb c) a).1 =
      CanonicalSupportWalk.walk c.source.tree
        (ForwardQRooted.sourceRoot c) a.1 := by
  rfl

/-- On all first-l homogeneous MODEL INTERIOR addresses,
the realized original source interior both preserves and
reflects the model's OWN prefix order. This is the missing
interior/interior component of the canonical Q embedding. -/
theorem modelInterior_source_prefix_iff
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (a d : ModelInteriorVertex c) :
    IsPrefix a.1 d.1 ↔
      IsPrefix ((modelInteriorSourceEquiv hb c) a).1
        ((modelInteriorSourceEquiv hb c) d).1 := by
  have hcount := cut_heapIndex_succ_eq_l hb c
  have haLe : heapIndex a.1 ≤ heapIndex (cutAddress c).1 := by
    have ha : heapIndex a.1 < l := a.2
    omega
  have hdLe : heapIndex d.1 ≤ heapIndex (cutAddress c).1 := by
    have hd : heapIndex d.1 < l := d.2
    omega
  let u : SourceAddress c :=
    ⟨a.1, heap_le_cut_admissible hb c a.1 haLe⟩
  let v : SourceAddress c :=
    ⟨d.1, heap_le_cut_admissible hb c d.1 hdLe⟩
  rw [modelInteriorSourceEquiv_value hb c a,
    modelInteriorSourceEquiv_value hb c d]
  exact sourceAddress_prefix_iff c u v

end DualTree.ForwardSourceAddressPrefixIso
