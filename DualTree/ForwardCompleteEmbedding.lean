import DualTree.CanonicalForwardAuxIso
import DualTree.ImmediateSupportHeight
import DualTree.CompleteInteriorBranching

/-!
# The canonical embedding for genuinely forward-complete skew supports

The printed-order canonical map in CompleteSupportAddresses takes a
hypothesis `completeB paperAuxB k T = true`. This is not an acceptable
constructor for the globally forward-repaired Lemma 27: a finite tree
satisfying `completeB forwardAuxB k T = true` need not be complete in
the original reverse-lex class.

We rebuild the support-direction map directly from the generic
skew-tree successor geometry, with the *correct* forward-complete
hypothesis throughout. The complete skew clauses imply:
* a unique root and a unique successor in every ambient direction
  below level k-1;
* every bounded address follows a valid support path;
* the endpoint has intrinsic rank equal to its address length;
* the resulting support embedding preserves prefixes and ordinary
  forward lexicographic order.

The additional nonsingleton hypothesis is automatic at the early cut
used in Lemma 27, and will be removed from the main interface once the
general k=1 convention has been treated.

Surjectivity, inverse addresses, and full forward auxiliary order
isomorphism are separate follow-ups. In particular no theorem in
this file assumes that a forward-complete support is also complete
under the printed order.
-/

namespace DualTree.ForwardCompleteEmbedding

/-- The forward-complete skew support is duplicate-free. -/
theorem support_nodup {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true) :
    T.Nodup := by
  have hparts := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hparts
  have hskew := hparts.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  simpa using hskew.1

/-- A nonsingleton forward-complete skew support has a
root extending to every support vertex. -/
theorem exists_root {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1) :
    ∃ r : Node b, r ∈ T ∧
      ∀ t : Node b, t ∈ T → IsPrefix r t := by
  have hc := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hroot : SkewTree.rootedB T = true :=
    CompleteSkewMeet.rootedB_of_skew_nonSingleton
      SkewTree.forwardAuxB T hc.1 hnon
  unfold SkewTree.rootedB at hroot
  rcases List.any_eq_true.mp hroot with ⟨r, hr, htest⟩
  refine ⟨r, hr, ?_⟩
  intro t ht
  exact DirectionalSupport.prefix_of_isPrefixOf_true
    ((List.all_eq_true.mp htest) t ht)

/-- A fixed root chosen inside the forward-complete support. -/
noncomputable def rootOf {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1) : Node b :=
  Classical.choose (exists_root T hcomplete hnon)

theorem rootOf_mem {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1) :
    rootOf T hcomplete hnon ∈ T :=
  (Classical.choose_spec (exists_root T hcomplete hnon)).1

theorem rootOf_prefix {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : Node b) (ht : t ∈ T) :
    IsPrefix (rootOf T hcomplete hnon) t :=
  (Classical.choose_spec (exists_root T hcomplete hnon)).2 t ht

/-- Every level strictly before k-1 has all directional
immediate successors under the genuine forward skew axioms. -/
theorem branch_of_height_lt {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (s : Node b) (hs : s ∈ T)
    (hlevel : SkewTree.heightAt T s + 1 < k)
    (i : Fin b) :
    SkewTree.uniqueBranchB T s i = true := by
  have htotal :
      ∀ s t : Node b, s ≠ t →
      SkewTree.forwardAuxB s t = true ∨
      SkewTree.forwardAuxB t s = true := by
    intro s t _
    rcases CanonicalForwardAuxIso.forwardAux_total s t with h | h
    · exact Or.inl (by simpa [SkewTree.forwardAuxB] using h)
    · exact Or.inr (by simpa [SkewTree.forwardAuxB] using h)
  exact CompleteInteriorBranching.fullDirections_of_complete_nonleaf_total
    SkewTree.forwardAuxB T hcomplete hnon htotal s hs
    (CompleteInteriorBranching.nonleaf_of_height_lt
      SkewTree.forwardAuxB T hcomplete s hs hlevel) i

/-- A uniform induction proves admissibility and exact intrinsic
rank for any path whose starting rank plus length is below k. -/
theorem admissible_and_height {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1) :
    ∀ (address s : Node b),
      s ∈ T →
      SkewTree.heightAt T s + address.length < k →
      CanonicalSupportWalk.Admissible T s address ∧
      SkewTree.heightAt T
        (CanonicalSupportWalk.walk T s address) =
        SkewTree.heightAt T s + address.length := by
  intro address
  induction address with
  | nil =>
      intro s hs hbudget
      exact ⟨trivial, rfl⟩
  | cons i tail ih =>
      intro s hs hbudget
      have hlevel : SkewTree.heightAt T s + 1 < k := by
        simp only [List.length_cons] at hbudget
        omega
      have hbranch : SkewTree.uniqueBranchB T s i = true :=
        branch_of_height_lt T hcomplete hnon s hs hlevel i
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
            (CanonicalSupportWalk.walk T
              (CanonicalSupportWalk.next T s i) tail) =
          SkewTree.heightAt T s + (i :: tail).length
        rw [htail_rank, hnext_rank]
        simp only [List.length_cons]
        omega

/-- The genuine forward canonical support walk based at the
chosen forward-complete root. -/
noncomputable def canonicalWalk {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (address : Node b) : Node b :=
  CanonicalSupportWalk.walk T (rootOf T hcomplete hnon) address

/-- All bounded source addresses are admissible and land in the
forward-complete support at precisely their source lengths. -/
theorem canonical_bounded_address {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (address : Node b)
    (haddress : InHomTree k address) :
    CanonicalSupportWalk.Admissible T
      (rootOf T hcomplete hnon) address ∧
    canonicalWalk T hcomplete hnon address ∈ T ∧
    SkewTree.heightAt T
      (canonicalWalk T hcomplete hnon address) =
      address.length := by
  let root := rootOf T hcomplete hnon
  have hrank : SkewTree.heightAt T root = 0 :=
    ImmediateSupportHeight.heightAt_root_zero T root
      (rootOf_prefix T hcomplete hnon)
  have hbudget : SkewTree.heightAt T root + address.length < k := by
    have ha : address.length < k := haddress
    omega
  obtain ⟨hvalid, hheight⟩ :=
    admissible_and_height T hcomplete hnon address root
      (rootOf_mem T hcomplete hnon) hbudget
  refine ⟨hvalid, ?_, ?_⟩
  · exact CanonicalSupportWalk.walk_mem_of_admissible T
      root address (rootOf_mem T hcomplete hnon) hvalid
  · simpa [canonicalWalk, root, hrank] using hheight

/-- The actual bounded complete-skew embedding for the
globally corrected auxiliary-order class. -/
noncomputable def canonicalEmbedding {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1) :
    BoundedNode b k → {t : Node b // t ∈ T} :=
  fun u =>
    ⟨canonicalWalk T hcomplete hnon u.1,
      (canonical_bounded_address
        T hcomplete hnon u.1 u.2).2.1⟩

theorem canonicalEmbedding_height {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (u : BoundedNode b k) :
    SkewTree.heightAt T
      (canonicalEmbedding T hcomplete hnon u).1 =
      u.1.length :=
  (canonical_bounded_address
    T hcomplete hnon u.1 u.2).2.2

theorem canonicalEmbedding_prefix {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (u v : BoundedNode b k)
    (huv : IsPrefix u.1 v.1) :
    IsPrefix
      (canonicalEmbedding T hcomplete hnon u).1
      (canonicalEmbedding T hcomplete hnon v).1 :=
  CanonicalSupportWalk.walk_prefix T
    (rootOf T hcomplete hnon) huv

/-- The corrected complete-skew embedding is injective,
by the already generic admissible-walk injectivity lemma. -/
theorem canonicalEmbedding_injective {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1) :
    Function.Injective (canonicalEmbedding T hcomplete hnon) := by
  intro u v heq
  have hu : CanonicalSupportWalk.Admissible T
      (rootOf T hcomplete hnon) u.1 :=
    (canonical_bounded_address T hcomplete hnon u.1 u.2).1
  have hv : CanonicalSupportWalk.Admissible T
      (rootOf T hcomplete hnon) v.1 :=
    (canonical_bounded_address T hcomplete hnon v.1 v.2).1
  have himages :
      canonicalWalk T hcomplete hnon u.1 =
        canonicalWalk T hcomplete hnon v.1 :=
    congrArg Subtype.val heq
  have haddresses : u.1 = v.1 :=
    CanonicalSupportInjective.walk_injective_of_admissible
      T u.1 (rootOf T hcomplete hnon) v.1
      hu hv himages
  exact Subtype.ext haddresses

/-- The corrected embedding preserves ordinary forward
lexicographic order on every pair of bounded addresses. -/
theorem canonicalEmbedding_lex_mono {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (u v : BoundedNode b k)
    (hlex : FinLexLE u.1 v.1) :
    FinLexLE
      (canonicalEmbedding T hcomplete hnon u).1
      (canonicalEmbedding T hcomplete hnon v).1 := by
  have hu : CanonicalSupportWalk.Admissible T
      (rootOf T hcomplete hnon) u.1 :=
    (canonical_bounded_address T hcomplete hnon u.1 u.2).1
  have hv : CanonicalSupportWalk.Admissible T
      (rootOf T hcomplete hnon) v.1 :=
    (canonical_bounded_address T hcomplete hnon v.1 v.2).1
  change FinLexLE
    (CanonicalSupportWalk.walk T (rootOf T hcomplete hnon) u.1)
    (CanonicalSupportWalk.walk T (rootOf T hcomplete hnon) v.1)
  exact CanonicalForwardAux.walk_lex_of_admissible
    T u.1 (rootOf T hcomplete hnon) v.1 hu hv hlex

/-- The true forward-complete canonical map preserves the
forward auxiliary order, with no printed-order assumption. -/
theorem canonicalEmbedding_forward_mono {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (u v : BoundedNode b k)
    (hforward : ForwardAux u.1 v.1) :
    ForwardAux
      (canonicalEmbedding T hcomplete hnon u).1
      (canonicalEmbedding T hcomplete hnon v).1 := by
  have hc := hcomplete
  simp only [SkewTree.completeB, Bool.and_eq_true] at hc
  have hskew := hc.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  have hrest := hskew.2
  simp [hnon, Bool.and_eq_true] at hrest
  have hII : SkewTree.condIIB T = true := hrest.1.1.2
  have hIII : SkewTree.condIIIB T = true := hrest.1.2
  let I := canonicalEmbedding T hcomplete hnon
  rcases hforward with hlen | ⟨heq, hlex⟩
  · have hrank : SkewTree.heightAt T (I u).1 <
        SkewTree.heightAt T (I v).1 := by
      simpa only [I, canonicalEmbedding_height] using hlen
    exact ForwardOrderCompatibility.forwardAux_of_lower_height
      T hIII (I u).2 (I v).2 hrank
  · have htargetLex : FinLexLE (I u).1 (I v).1 :=
      canonicalEmbedding_lex_mono T hcomplete hnon u v hlex
    have hrank : SkewTree.heightAt T (I u).1 =
        SkewTree.heightAt T (I v).1 := by
      simpa only [I, canonicalEmbedding_height] using heq
    exact ForwardOrderCompatibility.forwardAux_of_equal_height_lex
      T hII (I u).2 (I v).2 hrank htargetLex

end DualTree.ForwardCompleteEmbedding
