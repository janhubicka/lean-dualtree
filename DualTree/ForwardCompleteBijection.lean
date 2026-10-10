import DualTree.ForwardCompleteEmbedding
import DualTree.CompleteSupportSurjective

/-!
# Bijection and inverse for genuinely forward-complete skew supports

The corrected global auxiliary-order convention changes which finite
supports count as k-complete skew trees. It is invalid to reuse the
source-specific canonicalEmbedding whose assumption is
`completeB paperAuxB k T = true`.

The preceding ForwardCompleteEmbedding module constructs the
canonical map under the *forward* complete-skew hypothesis,
proving admissibility, the exact support height, injectivity,
prefix preservation, and forward-order monotonicity.

We now prove surjectivity and an actual inverse for that map.
The key support-to-address argument is factored through generic
path reachability: if every immediate successor lies in a unique
direction and every non-leaf has all directions, then repeated
immediate-support steps yield an admissible source address.
The proof is independent of the printed-order canonical map.

Combining this with the already generic terminal-extension and
intrinsic-rank bounds proves the forward canonical embedding is
a bijection with a rank-correct inverse.

A final theorem establishes forward auxiliary-order *reflection*
by linearity plus injectivity, so that the corrected map becomes
an order isomorphism for genuinely forward-complete supports.
The corrected cone projection, Q-support and word are separate.
-/

namespace DualTree.ForwardCompleteBijection

/-- In a nonsingleton complete forward skew support, every
specified immediate successor is witnessed by the uniquely
determined immediate successor in its ambient direction. -/
theorem unique_direction_of_immediate {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (s u : Node b) (hs : s ∈ T)
    (hstep : SkewTree.immediateSuccB T s u = true)
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
  have huSucc : u ∈ SkewTree.immediateSuccs T s := by
    change u ∈ T.filter
      (fun t => SkewTree.immediateSuccB T s t)
    have huT :=
      ((SkewBranchGeometry.immediateSuccB_iff T s u).1 hstep).1
    exact List.mem_filter.mpr ⟨huT, hstep⟩
  have hnonleaf : (SkewTree.immediateSuccs T s).length ≠ 0 := by
    intro hzero
    have hnil : SkewTree.immediateSuccs T s = [] := by
      cases hslist : SkewTree.immediateSuccs T s with
      | nil => rfl
      | cons v vs => simp [hslist] at hzero
    simp [hnil] at huSucc
  exact CompleteInteriorBranching.fullDirections_of_complete_nonleaf_total
    SkewTree.forwardAuxB T hcomplete hnon htotal
    s hs hnonleaf i

/-- Walk from any support vertex to any support descendant in
a nonsingleton forward-complete skew tree, along the unique
sequence of ambient successor directions. -/
theorem walk_address_of_prefix_forward {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (s t : Node b)
    (hs : s ∈ T) (ht : t ∈ T)
    (hst : IsPrefix s t) :
    ∃ address : Node b,
      CanonicalSupportWalk.Admissible T s address ∧
      CanonicalSupportWalk.walk T s address = t := by
  have hmain : ∀ d : Nat, ∀ s t : Node b,
      s ∈ T → t ∈ T → IsPrefix s t →
      t.length - s.length = d →
      ∃ address : Node b,
        CanonicalSupportWalk.Admissible T s address ∧
        CanonicalSupportWalk.walk T s address = t := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro s t hs ht hst hgap
        by_cases heq : s = t
        · subst t
          exact ⟨[], trivial, rfl⟩
        · have hstrict : IsStrictPrefix s t := ⟨hst, heq⟩
          obtain ⟨u, huT, hstep, hsu, hut⟩ :=
            SkewBranchGeometry.exists_first_immediate_on_path
              T s t ht hstrict
          obtain ⟨i, hdir⟩ :=
            SupportReachability.first_direction_of_strictPrefix hsu
          have hbranch : SkewTree.uniqueBranchB T s i = true :=
            unique_direction_of_immediate
              T hcomplete hnon s u hs hstep i
          have hnext : CanonicalSupportWalk.next T s i = u :=
            SupportReachability.next_eq_of_immediate
              T s u i hbranch hstep hdir
          have hsmaller : t.length - u.length < d := by
            have hsulen :=
              MeetClosedFromBranching.length_lt_of_strictPrefix hsu
            have hutlen := prefix_length_le hut
            omega
          obtain ⟨tail, hvalid, hwalk⟩ :=
            ih (t.length - u.length) hsmaller
              u t huT ht hut rfl
          refine ⟨i :: tail, ?_, ?_⟩
          · change SkewTree.uniqueBranchB T s i = true ∧
              CanonicalSupportWalk.Admissible T
                (CanonicalSupportWalk.next T s i) tail
            refine ⟨hbranch, ?_⟩
            rwa [hnext]
          · change CanonicalSupportWalk.walk T
              (CanonicalSupportWalk.next T s i) tail = t
            simpa [hnext] using hwalk
  exact hmain (t.length - s.length) s t hs ht hst rfl

/-- Every support vertex has intrinsic height below the
height parameter k of its genuinely forward-complete support. -/
theorem support_height_lt_k {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (t : Node b) (ht : t ∈ T) :
    SkewTree.heightAt T t < k := by
  obtain ⟨leaf, hleafMem, htleaf, hzero⟩ :=
    CompleteSupportSurjective.exists_terminal_above T t ht
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
  have hle : SkewTree.heightAt T t ≤
      SkewTree.heightAt T leaf := by
    by_cases heq : t = leaf
    · simp [heq]
    · exact Nat.le_of_lt
        (SupportHeightRanks.heightAt_lt_of_strictPrefix
          T ht ⟨htleaf, heq⟩)
  omega

/-- Every point of the forward-complete support has an
admissible root-based source address of the same length as
its intrinsic support rank. -/
theorem support_has_address {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : Node b) (ht : t ∈ T) :
    ∃ address : Node b,
      CanonicalSupportWalk.Admissible T
        (ForwardCompleteEmbedding.rootOf T hcomplete hnon) address ∧
      ForwardCompleteEmbedding.canonicalWalk
        T hcomplete hnon address = t ∧
      address.length = SkewTree.heightAt T t := by
  let root := ForwardCompleteEmbedding.rootOf T hcomplete hnon
  have hrootMem : root ∈ T :=
    ForwardCompleteEmbedding.rootOf_mem T hcomplete hnon
  have hrootPrefix : IsPrefix root t :=
    ForwardCompleteEmbedding.rootOf_prefix T hcomplete hnon t ht
  obtain ⟨address, hvalid, hwalk⟩ :=
    walk_address_of_prefix_forward
      T hcomplete hnon root t hrootMem ht hrootPrefix
  have hrootRank : SkewTree.heightAt T root = 0 :=
    ImmediateSupportHeight.heightAt_root_zero T root
      (ForwardCompleteEmbedding.rootOf_prefix T hcomplete hnon)
  have hrank :=
    SupportReachability.walk_height_of_admissible T
      (ForwardCompleteEmbedding.support_nodup T hcomplete)
      address root hrootMem hvalid
  have hlength : address.length = SkewTree.heightAt T t := by
    rw [hwalk, hrootRank] at hrank
    omega
  refine ⟨address, hvalid, ?_, hlength⟩
  simpa [ForwardCompleteEmbedding.canonicalWalk, root] using hwalk

/-- The true forward-complete canonical embedding is
surjective onto the finite support. -/
theorem canonicalEmbedding_surjective {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1) :
    Function.Surjective
      (ForwardCompleteEmbedding.canonicalEmbedding T hcomplete hnon) := by
  intro t
  obtain ⟨address, _hvalid, hmap, hlength⟩ :=
    support_has_address T hcomplete hnon t.1 t.2
  have hbound : address.length < k := by
    have hrank := support_height_lt_k T hcomplete t.1 t.2
    omega
  let u : BoundedNode b k := ⟨address, hbound⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  exact hmap

/-- The forward canonical embedding is a genuine finite
bijection, using its independently proved injectivity. -/
theorem canonicalEmbedding_bijective {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1) :
    Function.Bijective
      (ForwardCompleteEmbedding.canonicalEmbedding T hcomplete hnon) :=
  ⟨ForwardCompleteEmbedding.canonicalEmbedding_injective
      T hcomplete hnon,
    canonicalEmbedding_surjective T hcomplete hnon⟩

/-- The unique inverse address of a genuine
forward-complete support node. -/
noncomputable def inverseAddress {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T}) : BoundedNode b k :=
  Classical.choose (canonicalEmbedding_surjective T hcomplete hnon t)

theorem inverse_right {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T}) :
    ForwardCompleteEmbedding.canonicalEmbedding T hcomplete hnon
      (inverseAddress T hcomplete hnon t) = t :=
  Classical.choose_spec (canonicalEmbedding_surjective T hcomplete hnon t)

theorem inverse_left {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (u : BoundedNode b k) :
    inverseAddress T hcomplete hnon
      (ForwardCompleteEmbedding.canonicalEmbedding
        T hcomplete hnon u) = u :=
  (ForwardCompleteEmbedding.canonicalEmbedding_injective T hcomplete hnon)
    (inverse_right T hcomplete hnon
      (ForwardCompleteEmbedding.canonicalEmbedding T hcomplete hnon u))

/-- A forward-complete inverse address has length equal to
the original support node's intrinsic rank. -/
theorem inverse_length {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (t : {t : Node b // t ∈ T}) :
    (inverseAddress T hcomplete hnon t).1.length =
      SkewTree.heightAt T t.1 := by
  have hrank :=
    ForwardCompleteEmbedding.canonicalEmbedding_height
      T hcomplete hnon (inverseAddress T hcomplete hnon t)
  have hright :
      (ForwardCompleteEmbedding.canonicalEmbedding T hcomplete hnon
        (inverseAddress T hcomplete hnon t)).1 = t.1 :=
    congrArg Subtype.val (inverse_right T hcomplete hnon t)
  rw [hright] at hrank
  exact hrank.symm

/-- Every nonsingleton forward-complete support has a
canonical *order isomorphism*, not merely a monotone
embedding, for the corrected forward auxiliary order. -/
theorem canonicalEmbedding_forward_iff {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (hnon : T.length ≠ 1)
    (u v : BoundedNode b k) :
    ForwardAux u.1 v.1 ↔
      ForwardAux
        (ForwardCompleteEmbedding.canonicalEmbedding T hcomplete hnon u).1
        (ForwardCompleteEmbedding.canonicalEmbedding T hcomplete hnon v).1 := by
  constructor
  · exact ForwardCompleteEmbedding.canonicalEmbedding_forward_mono
      T hcomplete hnon u v
  · intro himages
    let I := ForwardCompleteEmbedding.canonicalEmbedding
      T hcomplete hnon
    rcases CanonicalForwardAuxIso.forwardAux_total u.1 v.1 with huv | hvu
    · exact huv
    · have hback : ForwardAux (I v).1 (I u).1 :=
        ForwardCompleteEmbedding.canonicalEmbedding_forward_mono
          T hcomplete hnon v u hvu
      have hEq : (I u).1 = (I v).1 :=
        CanonicalForwardAuxIso.forwardAux_antisymm himages hback
      have hSource : u = v :=
        (ForwardCompleteEmbedding.canonicalEmbedding_injective
          T hcomplete hnon) (Subtype.ext hEq)
      subst v
      exact CanonicalForwardAuxIso.forwardAux_refl u.1

end DualTree.ForwardCompleteBijection
