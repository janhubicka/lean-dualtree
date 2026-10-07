import DualTree.FullBeforeSignature

/-!
# The last interior vertex is the skew-tree branching witness

Clause (iv) of the definition of a skew tree has a unique final branching
node. Every node after this witness is a leaf, and the witness itself has
at least one successor. Consequently a maximal interior node coincides
with this branching witness.

This proves the missing bridge in Definition 26: the full-before property
at the last interior vertex follows from the skew-tree axioms, not from
an additional assumption. In particular, for a semi-complete starred
tree with nonempty interior, the exceptional leaves of the signature
have their boundary minima without any extra per-leaf hypotheses.

The remainder of signature transport and the surjectivity of Lemma 27's
coding map Q are still open.
-/

namespace DualTree.StarredSignature

/-- The interior of a singleton skew tree is empty. -/
theorem singleton_interior_nil {b : Nat} (t : Node b) :
    SkewTree.interior [t] = [] := by
  simp [SkewTree.interior, SkewTree.immediateSuccs,
    SkewTree.immediateSuccB, SkewTree.strictPrefixB]

/--
The last interior vertex is the branching witness from condition (iv).
No additional full-branching hypothesis is needed.
-/
theorem fullBefore_at_maxInterior
    {b n l : Nat} {α : Type*}
    {aux : Node b → Node b → Bool}
    (O : StarredWord b n l α aux)
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      aux t cut = true) :
    SkewTree.fullBeforeB aux O.tree cut = true := by
  have hcutS : cut ∈ O.tree := by
    have hh := hcut
    simp [SkewTree.interior] at hh
    aesop
  have hcutNotLeaf :
      (SkewTree.immediateSuccs O.tree cut).isEmpty = false := by
    have hh := hcut
    simp [SkewTree.interior] at hh
    aesop
  have hnonSingleton : O.tree.length ≠ 1 := by
    intro hlen
    cases hS : O.tree with
    | nil =>
        simp [hS] at hlen
    | cons root rest =>
        cases rest with
        | nil =>
            have hcutEq : cut = root := by
              simpa [hS] using hcutS
            subst cut
            have hnil : SkewTree.interior O.tree = [] := by
              rw [hS]
              exact singleton_interior_nil root
            rw [hnil] at hcut
            simp at hcut
        | cons x xs =>
            simp [hS] at hlen
  have hskew : SkewTree.skewB aux O.tree = true :=
    (Bool.and_eq_true.mp O.semi_complete).1
  have hIV : SkewTree.condIVB aux O.tree = true := by
    have hparts := (Bool.and_eq_true.mp hskew).2
    rcases Bool.or_eq_true.mp hparts with hsingle | hrest
    · have hlen : O.tree.length = 1 := by
        simpa using hsingle
      exact (hnonSingleton hlen).elim
    · have h := hrest
      simp only [Bool.and_eq_true] at h
      exact h.2
  unfold SkewTree.condIVB at hIV
  rcases List.any_eq_true.mp hIV with ⟨w, hwS, hwAny⟩
  rcases List.any_eq_true.mp hwAny with ⟨i, hi, hiPart⟩
  have hfull : SkewTree.fullBeforeB aux O.tree w = true := by
    have h := hiPart
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  have hempty : SkewTree.emptyAfterB aux O.tree w = true := by
    have h := hiPart
    simp only [Bool.and_eq_true] at h
    exact h.1.2
  have hpartial : SkewTree.partialAtB O.tree w i = true := by
    have h := hiPart
    simp only [Bool.and_eq_true] at h
    exact h.2
  have hchildren : (SkewTree.immediateSuccs O.tree w).length = i.val + 1 := by
    have h := (Bool.and_eq_true.mp hpartial).1
    simpa [SkewTree.partialAtB] using h
  have hwNonempty :
      (SkewTree.immediateSuccs O.tree w).isEmpty = false := by
    cases hS : SkewTree.immediateSuccs O.tree w with
    | nil =>
        simp [hS] at hchildren
    | cons x xs =>
        rfl
  have hwInterior : w ∈ SkewTree.interior O.tree := by
    simp [SkewTree.interior, hwS, hwNonempty]
  by_cases heq : w = cut
  · simpa [heq] using hfull
  · have hwBefore : aux w cut = true := hmax w hwInterior
    have htest : aux w cut && !(w == cut) = true := by
      simp [hwBefore, heq]
    have hcutLeaf :
        (SkewTree.immediateSuccs O.tree cut).isEmpty = true := by
      have hh := (List.all_eq_true.mp hempty) cut hcutS
      simpa [SkewTree.emptyAfterB, htest] using hh
    rw [hcutNotLeaf] at hcutLeaf
    cases hcutLeaf

/--
For an actual maximal interior cut of a starred tree, the signature
boundary tree is now defined without an extra full-before assumption.
-/
noncomputable def signatureTree_at_maxInterior
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredWord b n l α (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true) :
    List (Node b) :=
  signatureTree_of_fullBefore hb O cut hcut
    (fullBefore_at_maxInterior O cut hcut hmax)

/-- The new unconditional (at maximal interior cut) signature includes Int S. -/
theorem interior_mem_signatureTree_at_maxInterior
    {b n l : Nat} {α : Type*}
    (hb : 0 < b)
    (O : StarredWord b n l α (SkewTree.paperAuxB (b := b)))
    (cut : Node b)
    (hcut : cut ∈ SkewTree.interior O.tree)
    (hmax : ∀ t, t ∈ SkewTree.interior O.tree →
      SkewTree.paperAuxB t cut = true)
    {s : Node b}
    (hs : s ∈ SkewTree.interior O.tree) :
    s ∈ signatureTree_at_maxInterior hb O cut hcut hmax :=
  interior_mem_signatureTree_of_fullBefore hb O cut hcut
    (fullBefore_at_maxInterior O cut hcut hmax) hs

end DualTree.StarredSignature
