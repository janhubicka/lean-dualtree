import DualTree.ConeFrontier

/-!
# Ambient meets of finite tree nodes

The proof of Lemma 27 can avoid the earlier cone-meet condition by
establishing the usual geometric property that the support is closed
under the longest common initial segment (ambient meet).

This file defines the longest common prefix of two finite b-ary nodes
and proves that ambient meet-closure implies the cone-meet hypothesis
of ConeFrontier.  It does not assume that complete skew trees are
meet-closed: deriving this from their branch-direction axioms is the
remaining source-facing geometric theorem.
-/

namespace DualTree.MeetGeometry

/-- The longest common initial segment of two ambient tree nodes. -/
def commonPrefix {b : Nat} : Node b → Node b → Node b
  | [], _ => []
  | _, [] => []
  | a :: as, c :: cs =>
      if a = c then a :: commonPrefix as cs else []

/-- The ambient meet is an initial segment of its left argument. -/
theorem commonPrefix_prefix_left {b : Nat}
    (x y : Node b) : IsPrefix (commonPrefix x y) x := by
  induction x generalizing y with
  | nil =>
      exact ⟨[], by simp [commonPrefix]⟩
  | cons a as ih =>
      cases y with
      | nil =>
          exact ⟨a :: as, by simp [commonPrefix]⟩
      | cons c cs =>
          by_cases h : a = c
          · subst c
            rcases ih cs with ⟨u, hu⟩
            refine ⟨u, ?_⟩
            simpa [commonPrefix] using congrArg (List.cons a) hu
          · exact ⟨a :: as, by simp [commonPrefix, h]⟩

/-- Symmetry of the longest common prefix. -/
theorem commonPrefix_comm {b : Nat}
    (x y : Node b) : commonPrefix x y = commonPrefix y x := by
  induction x generalizing y with
  | nil =>
      cases y <;> rfl
  | cons a as ih =>
      cases y with
      | nil => rfl
      | cons c cs =>
          by_cases h : a = c
          · subst c
            simp [commonPrefix, ih]
          · have h' : c ≠ a := Ne.symm h
            simp [commonPrefix, h, h']

/-- The ambient meet is also an initial segment of its right argument. -/
theorem commonPrefix_prefix_right {b : Nat}
    (x y : Node b) : IsPrefix (commonPrefix x y) y := by
  rw [commonPrefix_comm]
  exact commonPrefix_prefix_left y x

/-- Common initial segments commute with attaching identical prefixes. -/
theorem commonPrefix_append_left {b : Nat}
    (s u v : Node b) :
    commonPrefix (s ++ u) (s ++ v) =
      s ++ commonPrefix u v := by
  induction s with
  | nil => rfl
  | cons a as ih =>
      simp [commonPrefix, ih]

/-- Every common prefix of two nodes precedes their ambient meet. -/
theorem prefix_commonPrefix {b : Nat}
    {s x y : Node b}
    (hsx : IsPrefix s x) (hsy : IsPrefix s y) :
    IsPrefix s (commonPrefix x y) := by
  rcases hsx with ⟨u, rfl⟩
  rcases hsy with ⟨v, rfl⟩
  refine ⟨commonPrefix u v, ?_⟩
  exact commonPrefix_append_left s u v

/-- A finite tree is closed under ambient meets. -/
def MeetClosed {b : Nat} (T : List (Node b)) : Prop :=
  ∀ x y, x ∈ T → y ∈ T → commonPrefix x y ∈ T

/-- Ambient meet-closure implies cone-meet-closure from Lemma 27. -/
theorem coneMeetClosed_of_meetClosed {b : Nat}
    (T : List (Node b)) (hT : MeetClosed T) :
    ConeFrontier.ConeMeetClosed T := by
  intro s x y hx hy hsx hsy
  refine ⟨commonPrefix x y, hT x y hx hy, ?_, ?_, ?_⟩
  · exact prefix_commonPrefix hsx hsy
  · exact commonPrefix_prefix_left x y
  · exact commonPrefix_prefix_right x y

/-- The cone-meet condition is strong enough to recover the actual ambient meet. -/
theorem meetClosed_of_coneMeetClosed {b : Nat}
    (T : List (Node b)) (hT : ConeFrontier.ConeMeetClosed T) :
    MeetClosed T := by
  intro x y hx hy
  obtain ⟨z, hz, hsz, hzx, hzy⟩ :=
    hT (commonPrefix x y) x y hx hy
      (commonPrefix_prefix_left x y)
      (commonPrefix_prefix_right x y)
  have hzs : IsPrefix z (commonPrefix x y) :=
    prefix_commonPrefix hzx hzy
  have heq : commonPrefix x y = z :=
    isPrefix_antisymm hsz hzs
  rw [heq]
  exact hz

/-- Cone-meet closure and closure under ambient longest common prefixes agree. -/
theorem coneMeetClosed_iff_meetClosed {b : Nat}
    (T : List (Node b)) :
    ConeFrontier.ConeMeetClosed T ↔ MeetClosed T :=
  ⟨meetClosed_of_coneMeetClosed T, coneMeetClosed_of_meetClosed T⟩

/-- The Lemma 27 frontier uniqueness statement with ambient meet closure. -/
theorem unique_frontier_of_boundary_of_meetClosed {b : Nat}
    (T : List (Node b)) (cut leaf s : Node b)
    (hT : MeetClosed T)
    (hb : SignatureBoundary.Boundary cut leaf s)
    (hdesc : ∃ t : Node b, t ∈ T ∧ IsPrefix s t) :
    ∃! f : Node b,
      CutFrontier.Frontier T (SignatureBoundary.BeforeCut cut) f ∧
      IsPrefix s f :=
  ConeFrontier.unique_frontier_of_signature_boundary T cut leaf s
    (coneMeetClosed_of_meetClosed T hT) hb hdesc

end DualTree.MeetGeometry
