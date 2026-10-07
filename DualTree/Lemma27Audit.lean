import DualTree.Basic
import DualTree.SpanAudit
import Mathlib

/-!
# Type and substitution checks for the proof of Lemma 27

The *statement* of Lemma 27 is not refuted here.  These are checks on the
actual construction printed on pp. 28--29.

(1) Its common tail height n-m' can make P_i leave b^{<n} whenever a frontier
    node has intrinsic depth m'+1.
(2) The demanded R_i surjection may be cardinally impossible without
    restricting its target to ancestors visible from the relevant cone.
(3) Deciding whether to retain a variable occurrence from the occurrence
    position, rather than from the variable root, need not preserve
    syntactic substitution.
-/

namespace DualTree.Lemma27Audit

/-- A frontier at depth m'+1=2 in the binary tree of height n=3. -/
def frontier : Node 2 := [(0 : Fin 2), (0 : Fin 2)]
def tail : Node 2 := [(0 : Fin 2)]

theorem frontier_in_tree : InHomTree 3 frontier := by
  decide

/-- The chosen tail lies in b^{<n-m'} with m'=1, n=3. -/
theorem tail_in_printed_domain : InHomTree 2 tail := by
  decide

/-- The concatenation required by the printed P_i is not in b^{<n}. -/
theorem printed_projection_address_overflows :
    ¬ InHomTree 3 (frontier ++ tail) := by
  decide

/-- One uniformly safe replacement is to reduce the tail height by one. -/
theorem safe_cone_tail
    {b n m : Nat} (s t : Node b)
    (hs : s.length ≤ m + 1)
    (hm : m + 1 ≤ n)
    (ht : t.length < n - (m + 1)) :
    InHomTree n (s ++ t) := by
  unfold InHomTree
  simp only [List.length_append]
  omega

/-- Two auxiliary symbols cannot cover three distinct interior variables. -/
theorem two_symbols_cannot_cover_three_variables :
    ¬ ∃ R : Fin 2 → Fin 3, Function.Surjective R := by
  rintro ⟨R, hR⟩
  have hcard : Fintype.card (Fin 3) ≤ Fintype.card (Fin 2) :=
    Fintype.card_le_of_surjective R hR
  norm_num at hcard

/-- A source word with one variable occurring twice. -/
def repeatedVariable : Fin 2 → Sum Bool (Fin 1) :=
  fun _ => Sum.inr 0

/-- Freeze just the second occurrence, but keep the first variable. -/
def splitVariable (i : Fin 2) : Sum Bool (Fin 1) :=
  if i.val = 0 then Sum.inr 0 else Sum.inl false

/-- No uniform substitution of the source word has this split variable fiber. -/
theorem occurrence_based_freezing_not_substitution :
    ¬ ∃ ρ : Fin 1 → Sum Bool (Fin 1),
      splitVariable = SpanAudit.substitute repeatedVariable ρ := by
  rintro ⟨ρ, hρ⟩
  have h0 := congrFun hρ (0 : Fin 2)
  have h1 := congrFun hρ (1 : Fin 2)
  have hsame : splitVariable (0 : Fin 2) = splitVariable (1 : Fin 2) := by
    calc
      splitVariable 0 = SpanAudit.substitute repeatedVariable ρ 0 := h0
      _ = SpanAudit.substitute repeatedVariable ρ 1 := rfl
      _ = splitVariable 1 := h1.symm
  simp [splitVariable] at hsame

end DualTree.Lemma27Audit
