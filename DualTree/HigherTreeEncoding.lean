import DualTree.HigherFirstVariable

/-!
# Track C: pull a coloring of actual finite-tree words to flat root/cone data

Root and cone Hales--Jewett coordinates are embedded in a SINGLE genuine
finite b-branching tree. Unused tree nodes receive a fixed fallback.
This yields a positive monochromatic rectangular family for arbitrary
colorings of true tree words, while retaining exact values at every embedded
cell. A remaining task is to identify that family as the span of a legal
complete-skew KVariableWord (and verify the selected branch-prefix laws).
-/

namespace DualTree.HigherTreeEncoding

open HigherConeAddresses
open HigherConeFreeze
open HigherConeRectangular
open HigherTreeCells
open HigherFirstVariable

/-- Total embedding of the root band and the complete cone-address matrix
into actual bounded tree words; values off those coordinates are fixed.
The two coordinate families are disjoint and each is injectively indexed. -/
noncomputable def encodeMatrix
    {b N M d : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (root : Fin N → Fin d → β)
    (cone : Fin M → Fin d → Address b N → β) :
    Fin d → BoundedNode b (N + M) → β := by
  classical
  exact fun coord t =>
    if hroot : ∃ j : Fin N,
        rootBandCell (M := M) hb j = t then
      root (Classical.choose hroot) coord
    else if hcone : ∃ z : Address b N × Fin M,
        coneBandCell hb z.1 z.2 = t then
      cone (Classical.choose hcone).2 coord
        (Classical.choose hcone).1
    else fallback

/-- At the zero-spine root-band node, the encoded tree word recovers the
exact flat Hales--Jewett root letter. -/
theorem encodeMatrix_root
    {b N M d : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (root : Fin N → Fin d → β)
    (cone : Fin M → Fin d → Address b N → β)
    (coord : Fin d) (j : Fin N) :
    encodeMatrix hb fallback root cone coord
      (rootBandCell (M := M) hb j) = root j coord := by
  classical
  unfold encodeMatrix
  split_ifs with hroot
  · have hj : Classical.choose hroot = j :=
      rootBandCell_injective hb (Classical.choose_spec hroot)
    simpa only [hj]
  all_goals exact (hroot ⟨j, rfl⟩).elim

/-- At every depth-N address and cone-band index, the encoded tree word
recovers that original (non-frozen) matrix entry exactly. -/
theorem encodeMatrix_cone
    {b N M d : Nat} {β : Type*}
    (hb : 0 < b) (fallback : β)
    (root : Fin N → Fin d → β)
    (cone : Fin M → Fin d → Address b N → β)
    (coord : Fin d) (a : Address b N) (j : Fin M) :
    encodeMatrix hb fallback root cone coord
      (coneBandCell hb a j) = cone j coord a := by
  classical
  unfold encodeMatrix
  split_ifs with hroot hcone
  · obtain ⟨k, hk⟩ := hroot
    exact (rootBandCell_ne_coneBandCell hb k a j hk).elim
  · have hz : Classical.choose hcone = (a, j) :=
      coneBandCell_pair_injective hb (Classical.choose_spec hcone)
    simpa only [hz]
  · exact (hcone ⟨(a, j), rfl⟩).elim

/-- Genuine tree-coloring pullback of the independent root-and-cone HJ
rectangle. The root and cone first-variable positions are also selected,
avoiding the later below-root obstruction. This does not yet assert the
family is a k=2 complete-skew variable-word span. -/
theorem exists_monochromatic_encoded_root_and_cones
    (b : Nat) (hb : 0 < b)
    (β γ : Type*) [Finite β] [Finite γ]
    (d : Nat) (fallback : β) :
    ∃ N M : Nat,
      ∀ C : (Fin d → BoundedNode b (N + M) → β) → γ,
        ∃ root : Fin N → Sum (Fin d → β) (Fin 1),
          ∃ r : Fin N,
            root r = Sum.inr 0 ∧
            (∀ j : Fin N, root j = Sum.inr 0 → r ≤ j) ∧
          ∃ cone : Fin M → Sum (Fin d → Address b N → β) (Fin 1),
            ∃ s : Fin M,
              cone s = Sum.inr 0 ∧
              (∀ j : Fin M, cone j = Sum.inr 0 → s ≤ j) ∧
              ∃ color : γ,
                ∀ σ : Fin 1 → Fin d → β,
                  ∀ τ : Fin d → Fin b → β,
                    C (encodeMatrix hb fallback
                      (SpanAudit.eval root σ)
                      (coneEvaluation hb r fallback cone τ)) = color := by
  obtain ⟨N, M, h⟩ :=
    exists_monochromatic_first_root_and_cone b hb β γ d fallback
  refine ⟨N, M, ?_⟩
  intro C
  let Cflat : (Fin N → Fin d → β) →
      (Fin M → Fin d → Address b N → β) → γ :=
    fun x y => C (encodeMatrix hb fallback x y)
  obtain ⟨root, r, hr, hrmin, cone, s, hs, hsmin, color, hmono⟩ :=
    h Cflat
  refine ⟨root, r, hr, hrmin, cone, s, hs, hsmin, color, ?_⟩
  intro σ τ
  exact hmono σ τ

end DualTree.HigherTreeEncoding
