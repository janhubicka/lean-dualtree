import DualTree.SupportReachability

/-!
# Surjectivity and inverse addresses of the complete-skew support map

Every point of a finite support extends to a terminal support vertex.
At a terminal vertex the k-complete condition fixes its intrinsic
height to k-1. Strict growth of height along support branches
therefore proves that every support vertex lies at height < k.

Combined with the already verified address construction, this shows
that every vertex is the image of a source address in b^{<k}. We
obtain a genuine bijection between source addresses and T and
construct its inverse, including the exact intrinsic length of the
inverse address. These are the missing algebraic pieces of I_T in
the cone projections of Lemma 27.

This does not yet prove that the bijection is an order isomorphism
in the repaired auxiliary linear order or validate Lemma 27's global
mixed-product coloring map Q.
-/

namespace DualTree.CompleteSupportSurjective

/-- The number of proper predecessors is never larger than the size
of the finite support list. No duplicate-freeness is needed. -/
theorem heightAt_le_length {b : Nat}
    (T : List (Node b)) (t : Node b) :
    SkewTree.heightAt T t ≤ T.length := by
  unfold SkewTree.heightAt SkewTree.preds
  induction T with
  | nil => simp
  | cons s rest ih =>
      cases h : SkewTree.strictPrefixB s t <;>
        simp [List.filter_cons, h] at ih ⊢ <;> omega

/-- Every support vertex has a terminal support descendant. -/
theorem exists_terminal_above {b : Nat}
    (T : List (Node b)) (t : Node b) (ht : t ∈ T) :
    ∃ leaf : Node b,
      leaf ∈ T ∧ IsPrefix t leaf ∧
      (SkewTree.immediateSuccs T leaf).length = 0 := by
  have hmain : ∀ d : Nat, ∀ t : Node b,
      t ∈ T →
      T.length - SkewTree.heightAt T t = d →
      ∃ leaf : Node b,
        leaf ∈ T ∧ IsPrefix t leaf ∧
        (SkewTree.immediateSuccs T leaf).length = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro s hs hgap
        by_cases hleaf : (SkewTree.immediateSuccs T s).length = 0
        · exact ⟨s, hs, isPrefix_refl s, hleaf⟩
        · cases hsucc : SkewTree.immediateSuccs T s with
          | nil =>
              simp [hsucc] at hleaf
          | cons u rest =>
              have huSucc : u ∈ SkewTree.immediateSuccs T s := by
                simp [hsucc]
              have hstep : SkewTree.immediateSuccB T s u = true := by
                change u ∈ T.filter
                  (fun z => SkewTree.immediateSuccB T s z) at huSucc
                exact (List.mem_filter.mp huSucc).2
              rcases (SkewBranchGeometry.immediateSuccB_iff T s u).1 hstep with
                ⟨huT, hsu, _⟩
              have hrank :
                  SkewTree.heightAt T s < SkewTree.heightAt T u :=
                SupportHeightRanks.heightAt_lt_of_strictPrefix T hs hsu
              have hboundS := heightAt_le_length T s
              have hboundU := heightAt_le_length T u
              have hsmall :
                  T.length - SkewTree.heightAt T u < d := by
                omega
              obtain ⟨leaf, hleafMem, huleaf, hzero⟩ :=
                ih (T.length - SkewTree.heightAt T u) hsmall
                  u huT rfl
              exact ⟨leaf, hleafMem,
                isPrefix_trans hsu.1 huleaf, hzero⟩
  exact hmain (T.length - SkewTree.heightAt T t) t ht rfl

/-- The intrinsic rank of every point in a k-complete skew support
is below k; this discharges the remaining size bound for inverse addresses. -/
theorem heightAt_lt_k {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : Node b) (ht : t ∈ T) :
    SkewTree.heightAt T t < k := by
  obtain ⟨leaf, hleafMem, htleaf, hzero⟩ :=
    exists_terminal_above T t ht
  have hc := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hrow := (List.all_eq_true.mp hc.2) leaf hleafMem
  change
    (if (SkewTree.immediateSuccs T leaf).length = 0
     then decide (SkewTree.heightAt T leaf + 1 = k)
     else decide ((SkewTree.immediateSuccs T leaf).length = b)) = true
    at hrow
  have hlast : SkewTree.heightAt T leaf + 1 = k := by
    simpa [hzero] using hrow
  have hle : SkewTree.heightAt T t ≤ SkewTree.heightAt T leaf := by
    by_cases heq : t = leaf
    · simp [heq]
    · exact Nat.le_of_lt
        (SupportHeightRanks.heightAt_lt_of_strictPrefix
          T ht ⟨htleaf, heq⟩)
  omega

/-- The finite canonical support embedding is surjective. -/
theorem canonicalEmbedding_surjective {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true) :
    Function.Surjective
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete) := by
  intro t
  obtain ⟨address, _hvalid, hmap, hlength⟩ :=
    SupportReachability.support_has_address T hcomplete t.1 t.2
  have hbound : address.length < k := by
    have hrank := heightAt_lt_k T hcomplete t.1 t.2
    omega
  let u : BoundedNode b k := ⟨address, hbound⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  exact hmap

/-- The canonical map is a bijection of b^{<k} with the support. -/
theorem canonicalEmbedding_bijective {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true) :
    Function.Bijective
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete) :=
  ⟨CanonicalSupportInjective.canonicalEmbedding_injective T hcomplete,
    canonicalEmbedding_surjective T hcomplete⟩

/-- The unique canonical source address corresponding to a support vertex. -/
noncomputable def inverseAddress {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T}) :
    BoundedNode b k :=
  Classical.choose (canonicalEmbedding_surjective T hcomplete t)

/-- The reconstructed source address maps back to the given support point. -/
theorem inverse_right {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T}) :
    CompleteSupportAddresses.canonicalEmbedding T hcomplete
      (inverseAddress T hcomplete t) = t :=
  Classical.choose_spec (canonicalEmbedding_surjective T hcomplete t)

/-- Canonical inversion also recovers the original bounded address. -/
theorem inverse_left {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (u : BoundedNode b k) :
    inverseAddress T hcomplete
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete u) = u :=
  (CanonicalSupportInjective.canonicalEmbedding_injective T hcomplete)
    (inverse_right T hcomplete
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete u))

/-- The inverse source address of a support point has length equal
to that point's intrinsic support height. -/
theorem inverse_length {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (t : {t : Node b // t ∈ T}) :
    (inverseAddress T hcomplete t).1.length =
      SkewTree.heightAt T t.1 := by
  have hrank :=
    CompleteSupportAddresses.canonicalEmbedding_height
      T hcomplete (inverseAddress T hcomplete t)
  have hright :
      (CompleteSupportAddresses.canonicalEmbedding T hcomplete
        (inverseAddress T hcomplete t)).1 = t.1 :=
    congrArg Subtype.val (inverse_right T hcomplete t)
  rw [hright] at hrank
  exact hrank.symm

end DualTree.CompleteSupportSurjective
