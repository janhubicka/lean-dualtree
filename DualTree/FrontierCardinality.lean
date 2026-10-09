import DualTree.FrontierSourcePadding
import DualTree.LiteralFrontierCount

/-!
# Counting the exact frontier coordinates of Lemma 27

Let T be a k-complete skew support, and cut at a support node of
intrinsic height m with m+1<k. Denote by F the minimal support
frontiers outside the inclusive auxiliary cut. Then

    |F| ≤ b^(m+1).

The proof does not infer this from rank inequalities alone. It maps
each frontier to its unique canonical inverse address, pads it to
length m+1, checks injectivity using the support-frontier antichain,
and bounds the size of the resulting finite set of words of
fixed length by the standard finite-word cardinality theorem.

The branching number b is explicitly assumed positive. In the
source applications b is positive; the degenerate b=0 case can
instead be eliminated from the early-cut completeness hypothesis.

This is the precise numerical estimate at the beginning of Lemma 27,
not yet the mixed-product coding Q or the full lemma.
-/

namespace DualTree.FrontierCardinality

/-- Map any support vertex to its padded canonical inverse address,
with an arbitrary fallback on nodes outside the support. -/
noncomputable def paddedSource {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (fill : Fin b) (depth : Nat)
    (s : Node b) : Node b := by
  classical
  exact if hs : s ∈ T then
    FrontierAntichainPadding.pad fill depth
      (CompleteSupportSurjective.inverseAddress T hcomplete ⟨s, hs⟩).1
  else []

/-- Distinct actual frontiers have distinct padded source addresses,
independently of their intrinsic heights. -/
theorem paddedSource_injective_frontiers {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (fill : Fin b) (depth : Nat)
    {f g : Node b}
    (hf : CutFrontier.Frontier T (fun x => PaperAux x cut) f)
    (hg : CutFrontier.Frontier T (fun x => PaperAux x cut) g)
    (hcodes :
      paddedSource T hcomplete fill depth f =
      paddedSource T hcomplete fill depth g) :
    f = g := by
  have hc :
      FrontierAntichainPadding.pad fill depth
        (CompleteSupportSurjective.inverseAddress T hcomplete
          ⟨f, hf.1⟩).1 =
      FrontierAntichainPadding.pad fill depth
        (CompleteSupportSurjective.inverseAddress T hcomplete
          ⟨g, hg.1⟩).1 := by
    simpa [paddedSource, hf.1, hg.1] using hcodes
  exact congrArg Subtype.val
    (FrontierSourcePadding.padded_frontier_injective
      T hcomplete cut ⟨f, hf.1⟩ ⟨g, hg.1⟩
      hf hg fill depth hc)

/-- The padded inverse addresses of actual frontiers all lie
at the common length m+1. -/
theorem paddedSource_frontier_length {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (fill : Fin b) (f : Node b)
    (hf : CutFrontier.Frontier T (fun x => PaperAux x cut) f) :
    (paddedSource T hcomplete fill (m+1) f).length = m+1 := by
  simpa [paddedSource, hf.1] using
    (FrontierSourcePadding.padded_frontier_length
      T hcomplete cut hcut hlevel hm ⟨f, hf.1⟩ hf fill)

/-- The literal list of minimal outside-cut frontiers
has at most b^(m+1) members. -/
theorem frontiers_length_le_pow {b k m : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut : Node b) (hcut : cut ∈ T)
    (hlevel : SkewTree.heightAt T cut + 1 < k)
    (hm : SkewTree.heightAt T cut = m)
    (hpos : 0 < b) :
    (LiteralFrontierCount.frontiers T cut).length ≤ b ^ (m + 1) := by
  classical
  let fill : Fin b := ⟨0, hpos⟩
  let F := LiteralFrontierCount.frontiers T cut
  let A : Finset (Node b) := F.toFinset
  let φ : Node b → Node b :=
    paddedSource T hcomplete fill (m + 1)
  let B : Finset (Node b) := A.image φ
  have hInjective : Set.InjOn φ (↑A) := by
    intro f hf g hg hfg
    have hfF : f ∈ F := by simpa [A] using hf
    have hgF : g ∈ F := by simpa [A] using hg
    have hfFront :=
      (LiteralFrontierCount.mem_frontiers_iff T cut f).1 hfF
    have hgFront :=
      (LiteralFrontierCount.mem_frontiers_iff T cut g).1 hgF
    exact paddedSource_injective_frontiers T hcomplete cut
      fill (m + 1) hfFront hgFront hfg
  have hMaps : Set.MapsTo φ (↑A) (↑B) := by
    intro f hf
    exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
  have hAB : A.card ≤ B.card :=
    Finset.card_le_card_of_injOn φ hMaps hInjective
  have hLength : ∀ w, w ∈ B → w.length = m+1 := by
    intro w hw
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hw
    have hfF : f ∈ F := by simpa [A] using hf
    have hfFront :=
      (LiteralFrontierCount.mem_frontiers_iff T cut f).1 hfF
    exact paddedSource_frontier_length T hcomplete
      cut hcut hlevel hm fill f hfFront
  have hFilter : B.filter (fun w => w.length = m+1) = B := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hw
      exact ⟨hw, hLength w hw⟩
  have hB : B.card ≤ b ^ (m+1) := by
    have hcount :
        (B.filter (fun w => w.length = m+1)).card ≤
          Fintype.card (Fin b) ^ (m+1) :=
      Finset.card_filter_length_eq_le
    rw [hFilter] at hcount
    simpa using hcount
  have hA : F.length = A.card := by
    exact List.toFinset_card_of_nodup
      (LiteralFrontierCount.frontiers_nodup T cut)
  rw [hA]
  exact hAB.trans hB

end DualTree.FrontierCardinality
