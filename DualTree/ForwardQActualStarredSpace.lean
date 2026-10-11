import DualTree.ForwardQCanonicalD2
import DualTree.ForwardQRetainedWordScaffold

/-!
# The actual corrected D₀/D₂ starred Q-input domain

The corrected source-facing Q construction uses a mixed-product
kind with no D₁ coordinates. Its selected D₂ indices are exactly
the finite subtype BulletIndex (kind c), ordered by their
underlying genuine sorted minimal T-frontier coordinates.

We now define, as an actual subtype of the mixed-product
element type Input c, the point family satisfying the vector
1-complete singleton condition in the *canonical* selected D₂
order. This prevents applying the geometric Q lemma to an
unrestricted mixed-product element.

The resulting actual starred-input subtype has a fully
semi-complete corrected Q support by the previously verified
conditional geometric theorem. It also admits a legal
starred-word witness using the original source word, provided
the enclosing T support is n-bounded. Such a witness proves
only well-typedness of the support/variable-root structure;
it is not the particular mixed-cone output word g_w of
Lemma 27 and proves nothing about colouring.

The definition here is specific to the corrected forward
auxiliary order, selected D₀/D₂ coordinates and safe local
tail height. No theorem identifies it with every instance
of the original paper's printed W_* domain.
-/

namespace DualTree.ForwardQActualStarredSpace

open ForwardSourceQTree
open ForwardQIndexedTRanks

/-- Corrected D₀/D₂ starred input condition on the actual
selected bullet coordinates, canonically enumerated by
their inherited forward-sorted frontier indices. -/
def IsStarred
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) : Prop :=
  VectorSkew.vectorCompleteB SkewTree.forwardAuxB 1
    (fun i : Fin (Fintype.card (MixedProduct.BulletIndex (kind c))) =>
      [(x.bulletPoint ((ForwardQCanonicalD2.orderedBulletIso c) i)).1]) = true

/-- An actual corrected-Q starred point is a genuinely typed
member of the mixed-product Input domain plus its vector-one
condition, rather than an unrestricted arbitrary Input. -/
abbrev StarredInput
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :=
  {x : Input c // IsStarred c x}

/-- Characterization of the corrected starred condition by the
exact selected D₂ marked-point length order. -/
theorem isStarred_iff_bullet_lengths_ordered
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c) :
    IsStarred c x ↔ BulletLengthsOrdered c x := by
  exact ForwardQCanonicalD2.canonical_vector_one_iff_bullet_lengths_ordered c x

/-- Every ordered-bullet mixed input can be equipped with the
precise corrected starred-domain proof, without specifying
any new or reindexed bullet coordinates. -/
def starredInputOfOrdered
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (x : Input c)
    (hordered : BulletLengthsOrdered c x) :
    StarredInput c :=
  ⟨x, (isStarred_iff_bullet_lengths_ordered c x).2 hordered⟩

/-- All actual members of the corrected starred D₀/D₂
input subtype give genuinely semi-complete forward-skew
Q supports, with no further side assumption on point order. -/
theorem actual_starred_Q_semiComplete
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : StarredInput c) :
    SkewTree.semiCompleteB SkewTree.forwardAuxB
      (nodes c x.1).toList = true := by
  exact ForwardQCanonicalD2.Q_semiComplete_of_canonical_D2_vectorOne
    hb c x.1 x.2

/-- The original source variable roots coincide with the
interior of the genuine reconstructed starred Q support,
rather than only with a hypothetical signature skeleton. -/
theorem actual_starred_Q_variable_roots
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : StarredInput c)
    (s : Node b) :
    s ∈ c.source.word.supportNodes ↔
      s ∈ SkewTree.interior (nodes c x.1).toList :=
  ForwardQRetainedWordScaffold.original_word_support_iff_Q_interior
    hb c x.1 s

/-- A placeholder starred word on an actual starred Q support
is well typed whenever the enclosing complete T is n-bounded.
The resulting word is the unchanged source word and therefore
must not be substituted for Lemma 27's required g_w. -/
noncomputable def placeholderStarredWordOnQ
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : StarredInput c)
    (hTbound : ∀ s : Node b, s ∈ c.T → InHomTree n s) :
    StarredSignature.StarredWord b n l α
      (SkewTree.forwardAuxB (b := b)) :=
  ForwardQRetainedWordScaffold.retained_source_word_witness
    hb c x.1 hTbound (actual_starred_Q_semiComplete hb c x)

/-- The placeholder starred-word support is literally the
actual reconstructed Q support, with no approximation. -/
theorem placeholderStarredWordOnQ_tree
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (x : StarredInput c)
    (hTbound : ∀ s : Node b, s ∈ c.T → InHomTree n s) :
    (placeholderStarredWordOnQ hb c x hTbound).tree =
      (nodes c x.1).toList := rfl

end DualTree.ForwardQActualStarredSpace
