import DualTree.ForwardModelHeapLevels
import DualTree.CanonicalForwardAuxIso

/-!
# Injectivity and exact forward order reflection of the heap model

The corrected forward model heap code has already been shown to
respect the length-first forward auxiliary order. The missing
algebraic fact is uniqueness of a direction list from its heap
index, for any positive branching arity b.

Every nonempty node is p ++ [i]. Its heap code is
    b * heapIndex(p) + 1 + i,  0 ≤ i < b.

If two such codes agree, their parent codes must agree:
if one parent had smaller code, the checked child-block order
would force strictly smaller child codes. Once the parent
codes agree, the child directions agree by cancellation.
Induction on the first list's length now proves uniqueness,
with no assumption on the second list's length.

Together with the verified cross-level separation and equal-level
lex comparison, this proves that heapIndex reflects as well as
preserves the CORRECTED length-first ForwardAux order.

This is an arithmetic model statement. It does not assert any
correspondence of model A with the literal R markers of a
forward-semi-complete skew output, nor restore the printed
reverse-lex order.
-/

namespace DualTree.ForwardModelHeapInjective

open ForwardModelBoundaryHeap
open ForwardModelHeapChildOrder
open ForwardModelHeapLexOrder
open ForwardModelHeapLevels

/-- The heap index uniquely determines its complete finite
direction sequence for every positive branching number. -/
theorem heapIndex_injective {b : Nat}
    (hb : 0 < b) :
    Function.Injective (heapIndex (b := b)) := by
  intro s t heq
  have hmain :
      ∀ (d : Nat) (s t : Node b),
        s.length = d →
        heapIndex s = heapIndex t →
        s = t := by
    intro d
    induction d with
    | zero =>
        intro s t hs heq
        cases s with
        | nil =>
            have htzero : heapIndex t = 0 := by
              simpa [heapIndex] using heq.symm
            have htbound :=
              ForwardModelBoundaryHeight.length_le_heapIndex hb t
            have htlength : t.length = 0 := by omega
            cases t with
            | nil => rfl
            | cons j tail => simp at htlength
        | cons i tail =>
            simp at hs
    | succ d ih =>
        intro s t hs heq
        cases hsrev : s.reverse with
        | nil =>
            have hsNil : s = [] := by
              have h := congrArg List.reverse hsrev
              simpa using h
            rw [hsNil] at hs
            simp at hs
        | cons i revParent =>
            let p : Node b := revParent.reverse
            have hsrepr : s = p ++ [i] := by
              have h := congrArg List.reverse hsrev
              simpa [p] using h
            cases htrev : t.reverse with
            | nil =>
                have htNil : t = [] := by
                  have h := congrArg List.reverse htrev
                  simpa using h
                have hzero : heapIndex (p ++ [i]) = 0 := by
                  rw [hsrepr, htNil] at heq
                  simpa [heapIndex] using heq
                have hpositive := heapIndex_lt_child hb p i
                omega
            | cons j revOther =>
                let q : Node b := revOther.reverse
                have htrepr : t = q ++ [j] := by
                  have h := congrArg List.reverse htrev
                  simpa [q] using h
                have hchildren :
                    heapIndex (p ++ [i]) =
                      heapIndex (q ++ [j]) := by
                  rw [← hsrepr, ← htrepr]
                  exact heq
                have hparent : heapIndex p = heapIndex q := by
                  rcases lt_trichotomy (heapIndex p) (heapIndex q)
                    with hlt | heqparent | hgt
                  · have hbad :=
                      heapIndex_child_lt_of_parent_lt p q i j hlt
                    omega
                  · exact heqparent
                  · have hbad :=
                      heapIndex_child_lt_of_parent_lt q p j i hgt
                    omega
                have hij : i = j := by
                  apply Fin.ext
                  have h := hchildren
                  rw [heapIndex_child, heapIndex_child, hparent] at h
                  omega
                have hpLen : p.length = d := by
                  rw [hsrepr] at hs
                  simp at hs
                  omega
                have hpq : p = q := ih p q hpLen hparent
                calc
                  s = p ++ [i] := hsrepr
                  _ = q ++ [j] := by rw [hpq, hij]
                  _ = t := htrepr.symm
  exact hmain s.length s t rfl heq

/-- Exact arithmetic characterization of the globally corrected
length-first forward auxiliary order. For positive b, it is
equivalent to ordinary nondecreasing b-ary heap indices. -/
theorem forwardAux_iff_heapIndex_le {b : Nat}
    (hb : 0 < b)
    (s t : Node b) :
    ForwardAux s t ↔ heapIndex s ≤ heapIndex t := by
  constructor
  · exact heapIndex_mono_of_forwardAux hb s t
  · intro hindex
    rcases lt_trichotomy s.length t.length with hlt | hlevel | hgt
    · exact Or.inl hlt
    · rcases lt_or_eq_of_le hindex with hstrict | heq
      · exact Or.inr
          ⟨hlevel,
           finLexLE_of_heapIndex_lt_same_length
             s t hlevel hstrict⟩
      · have hst : s = t := heapIndex_injective hb heq
        subst t
        exact CanonicalForwardAuxIso.forwardAux_refl s
    · have hbad :=
        heapIndex_lt_of_length_lt hb t s hgt
      omega

end DualTree.ForwardModelHeapInjective
