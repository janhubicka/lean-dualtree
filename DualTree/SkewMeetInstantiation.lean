import DualTree.CompleteSkewMeet

/-!
# Complete-skew meet closure for both auxiliary order conventions

The comparability hypothesis of CompleteSkewMeet follows from totality of
lexicographic comparison of finite lists. Thus every complete skew support
is ambient meet-closed, independently of the paper's order convention.
This does not repair the separate canonical-order counterexample.
-/

namespace DualTree.SkewMeetInstantiation

/-- The printed auxiliary order compares any two ambient nodes. -/
theorem paperAux_total {b : Nat} (s t : Node b) :
    PaperAux s t ∨ PaperAux t s := by
  rcases lt_trichotomy s.length t.length with hlt | heq | hgt
  · exact Or.inl (Or.inl hlt)
  · rcases finLexLE_total t s with hts | hst
    · exact Or.inl (Or.inr ⟨heq, hts⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hst⟩)
  · exact Or.inr (Or.inl hgt)

/-- The proposed forward-lex order is also total. -/
theorem forwardAux_total {b : Nat} (s t : Node b) :
    ForwardAux s t ∨ ForwardAux t s := by
  rcases lt_trichotomy s.length t.length with hlt | heq | hgt
  · exact Or.inl (Or.inl hlt)
  · rcases finLexLE_total s t with hst | hts
    · exact Or.inl (Or.inr ⟨heq, hst⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hts⟩)
  · exact Or.inr (Or.inl hgt)

/-- The executable version of printed auxiliary-order totality. -/
theorem paperAuxB_total {b : Nat} (s t : Node b) :
    SkewTree.paperAuxB s t = true ∨
      SkewTree.paperAuxB t s = true := by
  rcases paperAux_total s t with h | h
  · exact Or.inl (by simp [SkewTree.paperAuxB, h])
  · exact Or.inr (by simp [SkewTree.paperAuxB, h])

/-- The executable version of forward auxiliary-order totality. -/
theorem forwardAuxB_total {b : Nat} (s t : Node b) :
    SkewTree.forwardAuxB s t = true ∨
      SkewTree.forwardAuxB t s = true := by
  rcases forwardAux_total s t with h | h
  · exact Or.inl (by simp [SkewTree.forwardAuxB, h])
  · exact Or.inr (by simp [SkewTree.forwardAuxB, h])

/-- A singleton support is automatically ambient meet-closed. -/
theorem meetClosed_singleton {b : Nat} (s : Node b) :
    MeetGeometry.MeetClosed [s] := by
  intro x y hx hy
  have hxs : x = s := by simpa using hx
  have hys : y = s := by simpa using hy
  subst x
  subst y
  have hss : MeetGeometry.commonPrefix s s = s := by
    have h := MeetGeometry.commonPrefix_append_left
      s ([] : Node b) ([] : Node b)
    simpa [MeetGeometry.commonPrefix] using h
  simp [hss]

/-- All support lists of length one are ambient meet-closed. -/
theorem meetClosed_length_one {b : Nat}
    (T : List (Node b)) (hlen : T.length = 1) :
    MeetGeometry.MeetClosed T := by
  cases hT : T with
  | nil => simp [hT] at hlen
  | cons s rest =>
      cases rest with
      | nil =>
          simpa [hT] using meetClosed_singleton s
      | cons u us =>
          simp [hT] at hlen

/-- Every complete skew support under the printed order is ambient meet-closed. -/
theorem meetClosed_complete_paper {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.paperAuxB k T = true) :
    MeetGeometry.MeetClosed T := by
  by_cases hsingle : T.length = 1
  · exact meetClosed_length_one T hsingle
  · exact CompleteSkewMeet.meetClosed_of_complete_total
      SkewTree.paperAuxB T hcomplete hsingle
      (fun s t _ => paperAuxB_total s t)

/-- The same conclusion for complete skew supports under forward lex. -/
theorem meetClosed_complete_forward {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true) :
    MeetGeometry.MeetClosed T := by
  by_cases hsingle : T.length = 1
  · exact meetClosed_length_one T hsingle
  · exact CompleteSkewMeet.meetClosed_of_complete_total
      SkewTree.forwardAuxB T hcomplete hsingle
      (fun s t _ => forwardAuxB_total s t)

/-- Unique frontier above a signature boundary in a printed-order complete support. -/
theorem unique_frontier_complete_paper {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.paperAuxB k T = true)
    (cut leaf s : Node b)
    (hb : SignatureBoundary.Boundary cut leaf s)
    (hdesc : ∃ t : Node b, t ∈ T ∧ IsPrefix s t) :
    ∃! f : Node b,
      CutFrontier.Frontier T (SignatureBoundary.BeforeCut cut) f ∧
      IsPrefix s f :=
  MeetGeometry.unique_frontier_of_boundary_of_meetClosed
    T cut leaf s (meetClosed_complete_paper T hcomplete) hb hdesc

/-- The same frontier lemma for forward-lex supports, using the paper's cut. -/
theorem unique_frontier_complete_forward {b k : Nat}
    (T : List (Node b))
    (hcomplete :
      SkewTree.completeB SkewTree.forwardAuxB k T = true)
    (cut leaf s : Node b)
    (hb : SignatureBoundary.Boundary cut leaf s)
    (hdesc : ∃ t : Node b, t ∈ T ∧ IsPrefix s t) :
    ∃! f : Node b,
      CutFrontier.Frontier T (SignatureBoundary.BeforeCut cut) f ∧
      IsPrefix s f :=
  MeetGeometry.unique_frontier_of_boundary_of_meetClosed
    T cut leaf s (meetClosed_complete_forward T hcomplete) hb hdesc

end DualTree.SkewMeetInstantiation
