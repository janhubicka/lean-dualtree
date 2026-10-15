import DualTree.ForwardQPaperSelectorReduction
import DualTree.ForwardModelBoundaryHeap
import DualTree.CanonicalSupportWalk

/-!
# Uniqueness of the canonical directional walk on the partial first-l model

The paper explicitly introduces I_T for a complete skew support,
but Definition 24 applies I_U(a) to a semi-complete support U
with l interior nodes and external boundary A_l.

For positive l the relevant domain consists only of the first
l homogeneous interior addresses and their external children.
There is a simple generic uniqueness principle: any two maps of
the ambient address tree with the same root and the same local
directional successor recursion at each FIRST-l interior parent
must agree on every interior and external-boundary address.
No assumptions on how these maps behave outside that finite
domain are necessary.

This is proved by induction from the LAST direction of an address,
which has an interior parent whenever the whole address is in the
model interior or its external-child boundary.

We also make explicit the paper's exceptional l=0 convention:
its Definition 24 boundary is {[]} and NOT the external-child
boundary of an empty interior.

Consequently, to identify a published canonical I_U with the
verified model-to-Q map it suffices to check the Q root and local
unique-successor recursion on the first-l model parents.
The construction and verification of those Q local steps remain
the next concrete source-facing obligation.
-/

namespace DualTree.ForwardCanonicalPartialWalkUniqueness

open ForwardModelBoundaryHeap

/-- The paper's Definition 24 uses the external-child boundary
for positive l, but the singleton root when l=0. -/
def Definition24Boundary {b : Nat}
    (l : Nat) (a : Node b) : Prop :=
  if l = 0 then a = [] else ModelBoundary l a

/-- The l=0 case really is the singleton ROOT, not the
boundary of an empty first-l interior. -/
theorem definition24Boundary_zero_iff
    {b : Nat} (a : Node b) :
    Definition24Boundary 0 a ↔ a = [] := by
  simp [Definition24Boundary]

/-- For positive l, the Definition 24 boundary is exactly
the verified external-child homogeneous model A_l. -/
theorem definition24Boundary_pos_iff
    {b l : Nat} (hl : 0 < l) (a : Node b) :
    Definition24Boundary l a ↔ ModelBoundary l a := by
  simp [Definition24Boundary, Nat.ne_of_gt hl]

/-- Any nonempty initial-model vertex or external boundary
vertex has an interior parent, even when the model's first
l nodes do not form a complete level of the homogeneous tree. -/
theorem parent_interior_of_model_child
    {b l : Nat} (hb : 0 < b)
    (p : Node b) (i : Fin b)
    (ha : ModelInterior l (p ++ [i]) ∨
      ModelBoundary l (p ++ [i])) :
    ModelInterior l p := by
  rcases ha with hint | hboundary
  · exact modelInterior_prefix_closed hb ⟨[i], rfl⟩ hint
  · obtain ⟨q, j, hq, hwords⟩ := hboundary.2
    have hpref : IsPrefix p (q ++ [j]) := by
      rw [← hwords]
      exact ⟨[i], rfl⟩
    have hqref : IsPrefix q (q ++ [j]) := ⟨[j], rfl⟩
    have hlen : p.length = q.length := by
      have hh := congrArg List.length hwords
      simp only [List.length_append, List.length_singleton] at hh
      omega
    have hpq : IsPrefix p q :=
      CutFrontier.prefix_of_prefix_length_le hpref hqref
        (by omega)
    have hpeq : p = q :=
      CutPreservation.prefix_eq_of_length_eq hpq hlen
    simpa [hpeq] using hq

/-- RIGIDITY OF THE FIRST-l MODEL: two maps with the same
root and the same local outgoing-direction recursion at each
interior model vertex agree on the ENTIRE interior plus external
boundary, regardless of what they do elsewhere.

The shared local transition need not be a tree successor: the
lemma is pure finite-word induction and is reusable for arbitrary
semi-complete rooted supports. -/
theorem unique_on_model_of_local_step
    {b l : Nat} (hb : 0 < b)
    (step : Node b → Fin b → Node b)
    (F G : Node b → Node b)
    (hroot : F [] = G [])
    (hF : ∀ p i, ModelInterior l p →
      F (p ++ [i]) = step (F p) i)
    (hG : ∀ p i, ModelInterior l p →
      G (p ++ [i]) = step (G p) i)
    (a : Node b)
    (ha : ModelInterior l a ∨ ModelBoundary l a) :
    F a = G a := by
  induction a using List.reverseRecOn with
  | nil =>
      exact hroot
  | append_singleton p i ih =>
      have hp : ModelInterior l p :=
        parent_interior_of_model_child hb p i ha
      calc
        F (p ++ [i]) = step (F p) i := hF p i hp
        _ = step (G p) i :=
          congrArg (fun z : Node b => step z i)
            (ih (Or.inl hp))
        _ = G (p ++ [i]) := (hG p i hp).symm

/-- A purported canonical map with the true root and the
true unique-direction support transition agrees, at every
first-l interior or model-boundary address, with the concrete
canonical support walk. Agreement on arbitrary longer
addresses is NOT needed. -/
theorem unique_model_map_eq_support_walk
    {b l : Nat} (hb : 0 < b)
    (T : List (Node b))
    (root : Node b)
    (F : Node b → Node b)
    (hroot : F [] = root)
    (hstep : ∀ p i, ModelInterior l p →
      F (p ++ [i]) =
        CanonicalSupportWalk.next T (F p) i)
    (a : Node b)
    (ha : ModelInterior l a ∨ ModelBoundary l a) :
    F a = CanonicalSupportWalk.walk T root a := by
  have hwalkStep :
      ∀ p i, ModelInterior l p →
        CanonicalSupportWalk.walk T root (p ++ [i]) =
          CanonicalSupportWalk.next T
            (CanonicalSupportWalk.walk T root p) i := by
    intro p i _
    rw [CanonicalSupportWalk.walk_append]
    rfl
  exact unique_on_model_of_local_step hb
    (CanonicalSupportWalk.next T) F
    (CanonicalSupportWalk.walk T root)
    hroot hstep hwalkStep a ha

end DualTree.ForwardCanonicalPartialWalkUniqueness
