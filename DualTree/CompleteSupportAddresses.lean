import DualTree.ImmediateSupportHeight
import DualTree.CompleteInteriorBranching

/-!
# All addresses of a complete skew support

The directional support walk becomes an actual map on all source
addresses of length less than k. The invariant is simultaneously:
* each step is admissible (there is a unique successor in its direction);
* the intrinsic height of the endpoint is the starting height plus
  the number of directions already read.

Completeness supplies full directional branching below level k-1,
and the previously checked immediate-successor lemma supplies the
height increment. With the root of CompleteSupportRoot this yields
a source-facing map from the whole homogeneous b-ary tree b^{<k}
into the finite support, with correct intrinsic levels.

No injectivity or surjectivity onto T is claimed here yet.
-/

namespace DualTree.CompleteSupportAddresses

/-- Duplicate-freeness follows from the k-complete skew support condition. -/
theorem support_nodup {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true) :
    T.Nodup := by
  have hc := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hskew := hc.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  simpa using hskew.1

/-- Below the last intrinsic level every ambient direction has a
unique immediate successor of the finite support. -/
theorem branch_of_height_lt {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (s : Node b) (hs : s ∈ T)
    (hlevel : SkewTree.heightAt T s + 1 < k)
    (i : Fin b) :
    SkewTree.uniqueBranchB T s i = true := by
  have hnon : T.length ≠ 1 :=
    LiteralFrontierCleanup.nonsingleton_of_early_level
      T hcomplete s hs hlevel
  exact CompleteInteriorBranching.fullDirections_of_height_lt_paper
    T hcomplete hnon s hs hlevel i

/-- A single induction proves both admissibility of a source address
and the exact intrinsic height of its image under the support walk. -/
theorem admissible_and_height {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true) :
    ∀ (address s : Node b),
      s ∈ T →
      SkewTree.heightAt T s + address.length < k →
      CanonicalSupportWalk.Admissible T s address ∧
      SkewTree.heightAt T (CanonicalSupportWalk.walk T s address) =
        SkewTree.heightAt T s + address.length := by
  intro address
  induction address with
  | nil =>
      intro s hs hbudget
      constructor
      · trivial
      · rfl
  | cons i tail ih =>
      intro s hs hbudget
      have hlevel : SkewTree.heightAt T s + 1 < k := by
        simp only [List.length_cons] at hbudget
        omega
      have hbranch : SkewTree.uniqueBranchB T s i = true :=
        branch_of_height_lt T hcomplete s hs hlevel i
      have hnext_mem : CanonicalSupportWalk.next T s i ∈ T :=
        CanonicalSupportWalk.next_mem T s i hbranch
      have hnext_rank :
          SkewTree.heightAt T (CanonicalSupportWalk.next T s i) =
            SkewTree.heightAt T s + 1 :=
        ImmediateSupportHeight.heightAt_next T s i
          (support_nodup T hcomplete) hs hbranch
      have htail_budget :
          SkewTree.heightAt T (CanonicalSupportWalk.next T s i) +
            tail.length < k := by
        rw [hnext_rank]
        simp only [List.length_cons] at hbudget
        omega
      obtain ⟨htail_admissible, htail_rank⟩ :=
        ih (CanonicalSupportWalk.next T s i) hnext_mem htail_budget
      constructor
      · exact ⟨hbranch, htail_admissible⟩
      · change
          SkewTree.heightAt T
            (CanonicalSupportWalk.walk T (CanonicalSupportWalk.next T s i) tail) =
          SkewTree.heightAt T s + (i :: tail).length
        rw [htail_rank, hnext_rank]
        simp only [List.length_cons]
        omega

/-- Every source address in b^{<k} has an admissible path
and reaches the support at the expected intrinsic height. -/
theorem canonical_bounded_address {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (address : Node b)
    (haddress : InHomTree k address) :
    CanonicalSupportWalk.Admissible T
        (CompleteSupportRoot.rootOf T hcomplete) address ∧
      CompleteSupportRoot.canonicalWalk T hcomplete address ∈ T ∧
      SkewTree.heightAt T
        (CompleteSupportRoot.canonicalWalk T hcomplete address) =
        address.length := by
  let root := CompleteSupportRoot.rootOf T hcomplete
  have hrank : SkewTree.heightAt T root = 0 :=
    ImmediateSupportHeight.heightAt_root_zero T root
      (CompleteSupportRoot.rootOf_prefix T hcomplete)
  have hbudget : SkewTree.heightAt T root + address.length < k := by
    have ha : address.length < k := haddress
    omega
  obtain ⟨hvalid, hheight⟩ :=
    admissible_and_height T hcomplete address root
      (CompleteSupportRoot.rootOf_mem T hcomplete) hbudget
  refine ⟨hvalid, ?_, ?_⟩
  · exact CompleteSupportRoot.canonicalWalk_mem_of_admissible
      T hcomplete address hvalid
  · simpa [CompleteSupportRoot.canonicalWalk, root, hrank]
      using hheight

/-- The concrete image of a bounded address is a member of the
original support, without any extra admissibility hypothesis. -/
noncomputable def canonicalEmbedding {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true) :
    BoundedNode b k → {t : Node b // t ∈ T} :=
  fun u =>
    ⟨CompleteSupportRoot.canonicalWalk T hcomplete u.1,
      (canonical_bounded_address T hcomplete u.1 u.2).2.1⟩

/-- The canonical image of an address has its expected intrinsic level. -/
theorem canonicalEmbedding_height {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (u : BoundedNode b k) :
    SkewTree.heightAt T (canonicalEmbedding T hcomplete u).1 =
      u.1.length :=
  (canonical_bounded_address T hcomplete u.1 u.2).2.2

/-- The finite canonical embedding respects initial segments. -/
theorem canonicalEmbedding_prefix {b k : Nat}
    (T : List (Node b))
    (hcomplete : SkewTree.completeB SkewTree.paperAuxB k T = true)
    (u v : BoundedNode b k)
    (huv : IsPrefix u.1 v.1) :
    IsPrefix (canonicalEmbedding T hcomplete u).1
      (canonicalEmbedding T hcomplete v).1 :=
  CompleteSupportRoot.canonicalWalk_prefix T hcomplete huv

end DualTree.CompleteSupportAddresses
