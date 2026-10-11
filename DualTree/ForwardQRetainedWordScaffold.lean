import DualTree.ForwardQInteriorExact
import DualTree.ForwardQSourceTerminals
import DualTree.ForwardQSkewIV

/-!
# Source variable-root support on the actual reconstructed Q tree

A repaired Lemma 27 must build a new word g_w whose variable roots
are precisely the interior of its reconstructed Q support. The
geometric part already proves that the actual Q interior is exactly
the original source S interior.

This module isolates three simple but important consequences:
* if the ambient complete T support lies in the original homogeneous
  tree b^{<n}, every reconstructed Q node is also n-bounded;
* the source word's original variable roots are exactly the interior
  of the reconstructed Q support;
* the number of these roots remains the source dimension l.

As a structural sanity check, under the explicit premise that Q
is semi-complete skew, the *unchanged* original source variable
word can be packaged as a valid starred word on Q. This is only a
witness that the Q support has a legal rooted variable word; it is
NOT the new g_w prescribed by Lemma 27, which depends on the mixed
cone words and must satisfy a colouring pullback. The latter
construction remains an independent, unverified obligation.

The extra ambient bound on T is explicit: the existing Q Frame
alone does not state that all T nodes lie in b^{<n}.
-/

namespace DualTree.ForwardQRetainedWordScaffold

open ForwardSourceQTree

/-- The actual reconstructed Q support is n-bounded whenever
the enclosing ambient complete support T is n-bounded. -/
theorem Q_nodes_bounded_of_ambient_bound
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (hTbound : ∀ s : Node b, s ∈ c.T → InHomTree n s) :
    ∀ s : Node b, s ∈ (nodes c x).toList →
      InHomTree n s := by
  intro s hs
  have hsT : s ∈ c.T :=
    ForwardQSourceTerminals.Q_nodes_subset_complete
      c x s (Finset.mem_toList.mp hs)
  exact hTbound s hsT

/-- The original word has exactly the required roots in the
reconstructed Q support because Q retains the source interior
*exactly* (not only as a subset). -/
theorem original_word_support_iff_Q_interior
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (s : Node b) :
    s ∈ c.source.word.supportNodes ↔
      s ∈ SkewTree.interior (nodes c x).toList := by
  exact (c.source.support_eq_interior s).trans
    (ForwardQInteriorExact.Q_interior_iff_original hb c x s).symm

/-- Exact Q interior equality preserves the number l of
original source variable roots, even though the Q nodes are
held in a Finset-toList ordering different from source.tree. -/
theorem Q_interior_card_eq_source_dimension
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c) :
    (SkewTree.interior (nodes c x).toList).length = l := by
  classical
  have hQnodup :
      (SkewTree.interior (nodes c x).toList).Nodup := by
    unfold SkewTree.interior
    exact (Finset.nodup_toList (nodes c x)).filter _
  have hsourceSemi := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hsourceSemi
  have hsourceSkew := hsourceSemi.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hsourceSkew
  have hSourceNodup : c.source.tree.Nodup := by
    simpa using hsourceSkew.1
  have hSnodup :
      (SkewTree.interior c.source.tree).Nodup := by
    unfold SkewTree.interior
    exact hSourceNodup.filter _
  have hset :
      (SkewTree.interior (nodes c x).toList).toFinset =
      (SkewTree.interior c.source.tree).toFinset := by
    ext s
    simp only [List.mem_toFinset]
    exact ForwardQInteriorExact.Q_interior_iff_original hb c x s
  calc
    (SkewTree.interior (nodes c x).toList).length =
        (SkewTree.interior (nodes c x).toList).toFinset.card :=
      (List.toFinset_card_of_nodup hQnodup).symm
    _ = (SkewTree.interior c.source.tree).toFinset.card :=
      congrArg Finset.card hset
    _ = (SkewTree.interior c.source.tree).length :=
      List.toFinset_card_of_nodup hSnodup
    _ = l := c.source.interior_card

/-- A legal starred-word witness on Q can use the source's
old variable word if full Q semi-completeness and ambient
height bounds are supplied. This is NOT the intended
mixed-cone word g_w and asserts no colouring compatibility. -/
noncomputable def retained_source_word_witness
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (hTbound : ∀ s : Node b, s ∈ c.T → InHomTree n s)
    (hsemi :
      SkewTree.semiCompleteB SkewTree.forwardAuxB
        (nodes c x).toList = true) :
    StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) := {
  tree := (nodes c x).toList
  tree_bounded := Q_nodes_bounded_of_ambient_bound c x hTbound
  semi_complete := hsemi
  word := c.source.word
  interior_card := Q_interior_card_eq_source_dimension hb c x
  support_eq_interior := fun s =>
    original_word_support_iff_Q_interior hb c x s
  support_skew := c.source.support_skew
}

/-- The placeholder construction retains the actual Q support,
not an inferred signature tree or its ambient complete support. -/
theorem retained_source_word_witness_tree
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : Input c)
    (hTbound : ∀ s : Node b, s ∈ c.T → InHomTree n s)
    (hsemi :
      SkewTree.semiCompleteB SkewTree.forwardAuxB
        (nodes c x).toList = true) :
    (retained_source_word_witness hb c x hTbound hsemi).tree =
      (nodes c x).toList := rfl

end DualTree.ForwardQRetainedWordScaffold
