import DualTree.FrontierAntichainPadding
import DualTree.FrontierHeightBound

/-!
# Padding the actual inclusive-cut frontiers in source coordinates

For the d ≤ b^(m'+1) bound near Lemma 27, each minimal outside-cut
support frontier f has an inverse source address of length ≤ m'+1.
The inverse addresses form a prefix antichain by the already-proved
canonical prefix isomorphism and support frontier antichain.

Padding them all to length m'+1 is therefore injective. This file
checks that source-facing specialization, rather than relying only
on the generic list antichain statement.

The remaining arithmetic step is to count full-level b-ary words
of length m'+1, and identify d with the exact frontier list length.
-/

namespace DualTree.FrontierSourcePadding

/-- The inverse address of an actual frontier has height ≤ m'+1. -/
theorem inverse_frontier_rank_bound {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hcutHeight : SkewTree.heightAt T cut = m)
    (f : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun x => PaperAux x cut) f.1) :
    (CompleteSupportSurjective.inverseAddress T hcomplete f).1.length ≤
      m + 1 := by
  have hrank :=
    FrontierHeightBound.frontier_height_le_m_succ
      T cut f.1 hcomplete hcut hlevel hf hcutHeight
  have hinverse :=
    CompleteSupportSurjective.inverse_length T hcomplete f
  omega

/-- Inverse addresses of distinct outside-cut frontiers are
incomparable in the homogeneous source tree. -/
theorem inverse_frontier_antichain {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b)
    (f g : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun x => PaperAux x cut) f.1)
    (hg : CutFrontier.Frontier T (fun x => PaperAux x cut) g.1)
    (hprefix :
      IsPrefix
        (CompleteSupportSurjective.inverseAddress T hcomplete f).1
        (CompleteSupportSurjective.inverseAddress T hcomplete g).1) :
    f = g := by
  have himage :=
    CompleteSupportAddresses.canonicalEmbedding_prefix T hcomplete
      (CompleteSupportSurjective.inverseAddress T hcomplete f)
      (CompleteSupportSurjective.inverseAddress T hcomplete g) hprefix
  have hfimage :
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete
        (CompleteSupportSurjective.inverseAddress T hcomplete f)).1 = f.1 :=
    congrArg Subtype.val
      (CompleteSupportSurjective.inverse_right T hcomplete f)
  have hgimage :
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete
        (CompleteSupportSurjective.inverseAddress T hcomplete g)).1 = g.1 :=
    congrArg Subtype.val
      (CompleteSupportSurjective.inverse_right T hcomplete g)
  rw [hfimage, hgimage] at himage
  exact Subtype.ext
    (CutFrontier.frontier_antichain T
      (fun x => PaperAux x cut) hf hg himage)

/-- The padded inverse address of every frontier occupies the
common target level m'+1. -/
theorem padded_frontier_length {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hcutHeight : SkewTree.heightAt T cut = m)
    (f : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun x => PaperAux x cut) f.1)
    (fill : Fin b) :
    (FrontierAntichainPadding.pad fill (m + 1)
      (CompleteSupportSurjective.inverseAddress T hcomplete f).1).length =
        m + 1 := by
  exact FrontierAntichainPadding.pad_length fill (m + 1)
    (CompleteSupportSurjective.inverseAddress T hcomplete f).1
    (inverse_frontier_rank_bound T hcomplete cut hcut
      hlevel hcutHeight f hf)

/-- Two outside-cut frontiers with the same padded inverse
source address must be equal. -/
theorem padded_frontier_injective {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b)
    (f g : {t : Node b // t ∈ T})
    (hf : CutFrontier.Frontier T (fun x => PaperAux x cut) f.1)
    (hg : CutFrontier.Frontier T (fun x => PaperAux x cut) g.1)
    (fill : Fin b) (depth : Nat)
    (heq :
      FrontierAntichainPadding.pad fill depth
        (CompleteSupportSurjective.inverseAddress T hcomplete f).1 =
      FrontierAntichainPadding.pad fill depth
        (CompleteSupportSurjective.inverseAddress T hcomplete g).1) :
    f = g := by
  rcases FrontierAntichainPadding.comparable_of_pad_eq fill depth
      (CompleteSupportSurjective.inverseAddress T hcomplete f).1
      (CompleteSupportSurjective.inverseAddress T hcomplete g).1
      heq with hfg | hgf
  · exact inverse_frontier_antichain T hcomplete cut
      f g hf hg hfg
  · exact (inverse_frontier_antichain T hcomplete cut
      g f hg hf hgf).symm

end DualTree.FrontierSourcePadding
