import DualTree.CutPreservation

/-!
# Finite frontier decomposition at a cut

Let T be a finite set of tree nodes and let I be any distinguished subset.
The frontier is the set of nodes outside I which have no proper T-predecessor
outside I. Every node of T outside I lies above exactly one frontier node.

This is the abstract finite-tree geometry needed near the beginning of the
proof of Lemma 27: the minimal support nodes beyond the distinguished cut
index pairwise disjoint successor cones.

The proof does not assume that T is ambient-prefix closed (complete skew
subtrees need not be). Nor does it prove that every external signature boundary
node in the paper's set R is covered: those nodes may not belong to T, and
that additional source-facing interface remains open.
-/

namespace DualTree.CutFrontier

/-- A prefix of t agrees with the corresponding initial segment of t. -/
theorem take_length_of_prefix {b : Nat} {s t : Node b}
    (hst : IsPrefix s t) : t.take s.length = s := by
  rcases hst with ⟨u, rfl⟩
  simp

/-- Among two prefixes of the same node, the shorter prefixes the longer. -/
theorem prefix_of_prefix_length_le {b : Nat}
    {a c t : Node b}
    (hat : IsPrefix a t) (hct : IsPrefix c t)
    (hlen : a.length ≤ c.length) : IsPrefix a c := by
  have ha : t.take a.length = a := take_length_of_prefix hat
  have hc : t.take c.length = c := take_length_of_prefix hct
  have hac : c.take a.length = a := by
    calc
      c.take a.length = (t.take c.length).take a.length := by rw [hc]
      _ = t.take a.length := by
        simp [List.take_take, Nat.min_eq_left hlen,
          Nat.min_eq_right hlen]
      _ = a := ha
  refine ⟨c.drop a.length, ?_⟩
  calc
    c = c.take a.length ++ c.drop a.length :=
      (List.take_append_drop a.length c).symm
    _ = a ++ c.drop a.length := by rw [hac]

/--
A frontier node belongs to T, lies outside I, and has every proper
T-predecessor inside I.
-/
def Frontier {b : Nat}
    (T : List (Node b)) (I : Node b → Prop) (s : Node b) : Prop :=
  s ∈ T ∧ ¬ I s ∧
    ∀ r, r ∈ T → IsStrictPrefix r s → I r

/-- Two distinct frontier nodes can never be comparable in the tree. -/
theorem frontier_antichain {b : Nat}
    (T : List (Node b)) (I : Node b → Prop)
    {a c : Node b} (ha : Frontier T I a)
    (hc : Frontier T I c) (hac : IsPrefix a c) :
    a = c := by
  by_contra hneq
  exact ha.2.1 (hc.2.2 a ha.1 ⟨hac, hneq⟩)

/-- Every node of T outside I has some frontier ancestor. -/
theorem exists_frontier_above {b : Nat}
    (T : List (Node b)) (I : Node b → Prop)
    {t : Node b} (ht : t ∈ T) (hout : ¬ I t) :
    ∃ s, Frontier T I s ∧ IsPrefix s t := by
  classical
  have aux : ∀ n : Nat, ∀ t : Node b, t.length = n →
      t ∈ T → ¬ I t →
      ∃ s, Frontier T I s ∧ IsPrefix s t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u huLength huOutsideT huOutsideI
      by_cases hmin :
          ∀ s, s ∈ T → IsStrictPrefix s u → I s
      · exact ⟨u, ⟨huOutsideT, huOutsideI, hmin⟩,
          isPrefix_refl u⟩
      · push_neg at hmin
        rcases hmin with ⟨s, hsT, hsPre, hsOutside⟩
        have hshort : s.length < n := by
          have hle : s.length ≤ u.length :=
            prefix_length_le hsPre.1
          have hstrict : s.length < u.length := by
            by_contra hn
            have heqLen : s.length = u.length := by omega
            have heq : s = u :=
              CutPreservation.prefix_eq_of_length_eq hsPre.1 heqLen
            exact hsPre.2 heq
          omega
        rcases ih s.length hshort s rfl hsT hsOutside with
          ⟨root, hroot, hrPrefix⟩
        exact ⟨root, hroot, isPrefix_trans hrPrefix hsPre.1⟩
  exact aux t.length t rfl ht hout

/-- Two frontier nodes below a common tree node coincide. -/
theorem frontier_unique_above {b : Nat}
    (T : List (Node b)) (I : Node b → Prop)
    {a c t : Node b}
    (ha : Frontier T I a) (hc : Frontier T I c)
    (hat : IsPrefix a t) (hct : IsPrefix c t) :
    a = c := by
  rcases le_total a.length c.length with hle | hle
  · exact frontier_antichain T I ha hc
      (prefix_of_prefix_length_le hat hct hle)
  · exact (frontier_antichain T I hc ha
      (prefix_of_prefix_length_le hct hat hle)).symm

/-- Unique frontier cone containing an outside node. -/
theorem exists_unique_frontier_above {b : Nat}
    (T : List (Node b)) (I : Node b → Prop)
    {t : Node b} (ht : t ∈ T) (hout : ¬ I t) :
    ∃! s, Frontier T I s ∧ IsPrefix s t := by
  rcases exists_frontier_above T I ht hout with ⟨s, hs, hst⟩
  refine ⟨s, ⟨hs, hst⟩, ?_⟩
  intro u hu
  exact frontier_unique_above T I hu.1 hs hu.2 hst

/--
For the paper's auxiliary cut, every support node after t0 lies above a
unique minimal support node after t0. This does not yet cover boundary nodes
not themselves belonging to the original support.
-/
theorem paperCut_exists_unique_frontier {b : Nat}
    (T : List (Node b)) (cut : Node b)
    {t : Node b} (ht : t ∈ T) (hout : ¬ PaperAux t cut) :
    ∃! s, Frontier T (fun x => PaperAux x cut) s ∧
      IsPrefix s t :=
  exists_unique_frontier_above T (fun x => PaperAux x cut) ht hout

/-- The same minimal-cone decomposition for the forward-lex repair. -/
theorem forwardCut_exists_unique_frontier {b : Nat}
    (T : List (Node b)) (cut : Node b)
    {t : Node b} (ht : t ∈ T) (hout : ¬ ForwardAux t cut) :
    ∃! s, Frontier T (fun x => ForwardAux x cut) s ∧
      IsPrefix s t :=
  exists_unique_frontier_above T (fun x => ForwardAux x cut) ht hout

end DualTree.CutFrontier
