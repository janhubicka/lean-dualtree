import DualTree.CanonicalTheoremSpec

/-!
# Alphabet and colour transport for the corrected final theorem statements

The corrected targets use canonical finite alphabets `Fin ell` and colours
`Fin r`.  A source statement for arbitrary finite alphabets needs a genuine
transport of the words, rooted symbols, syntactic refinements and simplicity
predicate.  Renaming constants leaves every support root and every canonical
boundary point fixed, including the zero-interior selector.

The results below transport the actual Ramsey propositions and their eventual
bounds through equivalences.  They do not supply the Ramsey existence proof.
In particular they do not recover syntactic refinement from evaluated spans
over unary alphabets; all refinement transport is directly symbolic.
-/

namespace DualTree.TheoremAlphabetTransport

open CorrectedTheoremSpec

/-- Rename alphabet constants and leave the actual variable roots fixed. -/
def renameVariableWord {b n : Nat} {α β : Type*}
    (e : α ≃ β) (f : VariableWord b n α) : VariableWord b n β where
  support := f.support
  support_nodup := f.support_nodup
  word := fun s => Sum.map e id (f.word s)
  atRoot := by
    intro v
    simp only [f.atRoot v, Sum.map_inr, id_eq]
  below := by
    intro v s hs
    cases hf : f.word s with
    | inl a => simp [hf] at hs
    | inr u =>
        have huv : u = v := by simpa [hf] using hs
        subst u
        exact f.below v s hf

/-- Complete support geometry is unchanged by an alphabet equivalence. -/
def renameWord {b n k : Nat} {α β : Type*}
    (e : α ≃ β) (f : Word b n k α) : Word b n k β where
  toVariableWord := renameVariableWord e f.toVariableWord
  complete_support := f.complete_support

/-- The whole starred tree, its interior and its root support are retained. -/
def renameStarred {b n l : Nat} {α β : Type*}
    (e : α ≃ β) (U : Starred b n l α) : Starred b n l β where
  tree := U.tree
  tree_bounded := U.tree_bounded
  semi_complete := U.semi_complete
  word := renameVariableWord e U.word
  interior_card := U.interior_card
  support_eq_interior := U.support_eq_interior
  support_skew := U.support_skew

def renameWordObservation {b n : Nat} {α β : Type*}
    (e : α ≃ β) (w : WordObservation b n α) : WordObservation b n β :=
  fun s => Sum.map e id (w s)

def renameStarredObservation {b n : Nat} {α β : Type*}
    (e : α ≃ β) (O : StarredObservation b n α) :
    StarredObservation b n β :=
  (O.1, renameWordObservation e O.2)

private theorem map_inverse {κ : Type*} {α β : Type*}
    (e : α ≃ β) (x : Sum α κ) :
    Sum.map e.symm id (Sum.map e id x) = x := by
  cases x <;> simp

private theorem renameVariableWord_inverse {b n : Nat} {α β : Type*}
    (e : α ≃ β) (f : VariableWord b n α) :
    renameVariableWord e.symm (renameVariableWord e f) = f := by
  cases f with
  | mk support hnd word atRoot below =>
      simp only [renameVariableWord]
      congr 1
      funext s
      cases word s <;> simp

private theorem renameWord_inverse {b n k : Nat} {α β : Type*}
    (e : α ≃ β) (f : Word b n k α) :
    renameWord e.symm (renameWord e f) = f := by
  cases f with
  | mk f hc =>
      simp only [renameWord, renameVariableWord_inverse]

private theorem renameWordObservation_inverse {b n : Nat} {α β : Type*}
    (e : α ≃ β) (w : WordObservation b n α) :
    renameWordObservation e.symm (renameWordObservation e w) = w := by
  funext s
  exact map_inverse e (w s)

private theorem renameWordObservation_inverse' {b n : Nat} {α β : Type*}
    (e : α ≃ β) (w : WordObservation b n β) :
    renameWordObservation e (renameWordObservation e.symm w) = w := by
  simpa only [Equiv.symm_symm] using renameWordObservation_inverse e.symm w

private theorem renameStarredObservation_inverse {b n : Nat} {α β : Type*}
    (e : α ≃ β) (O : StarredObservation b n α) :
    renameStarredObservation e.symm (renameStarredObservation e O) = O := by
  exact Prod.ext rfl (renameWordObservation_inverse e O.2)

private theorem renameStarredObservation_inverse' {b n : Nat} {α β : Type*}
    (e : α ≃ β) (O : StarredObservation b n β) :
    renameStarredObservation e (renameStarredObservation e.symm O) = O := by
  simpa only [Equiv.symm_symm] using renameStarredObservation_inverse e.symm O

private theorem underlyingSymbol_rename {b n : Nat} {α β : Type*}
    (e : α ≃ β) (f : VariableWord b n α) (s : BoundedNode b n) :
    CutPreservation.underlyingSymbol (renameVariableWord e f) s =
      Sum.map e id (CutPreservation.underlyingSymbol f s) := by
  cases hs : f.word s <;>
    simp [CutPreservation.underlyingSymbol, renameVariableWord, hs]

/-- Renaming a complete word agrees with renaming its semantic observation. -/
theorem wordObserve_rename {b n k : Nat} {α β : Type*}
    (e : α ≃ β) (f : Word b n k α) :
    wordObserve (renameWord e f) = renameWordObservation e (wordObserve f) := by
  funext s
  exact underlyingSymbol_rename e f.toVariableWord s

/-- Starred semantic observations retain the same finite tree and root names. -/
theorem starredObserve_rename {b n l : Nat} {α β : Type*}
    (e : α ≃ β) (U : Starred b n l α) :
    starredObserve (renameStarred e U) =
      renameStarredObservation e (starredObserve U) := by
  apply Prod.ext
  · rfl
  · funext s
    exact underlyingSymbol_rename e U.word s

private theorem map_substitute {ι κ₁ κ₂ : Type*} {α β : Type*}
    (e : α ≃ β) (w : ι → Sum α κ₁) (ρ : κ₁ → Sum α κ₂) :
    (fun s => Sum.map e id (SpanAudit.substitute w ρ s)) =
      SpanAudit.substitute (fun s => Sum.map e id (w s))
        (fun v => Sum.map e id (ρ v)) := by
  funext s
  cases hw : w s <;> simp [SpanAudit.substitute, hw]

private theorem rename_substitution {b n : Nat} {α β : Type*}
    (e : α ≃ β) (f g : VariableWord b n α)
    (h : ∃ ρ : f.Vars → Sum α g.Vars,
      g.word = SpanAudit.substitute f.word ρ) :
    ∃ ρ : (renameVariableWord e f).Vars →
        Sum β (renameVariableWord e g).Vars,
      (renameVariableWord e g).word =
        SpanAudit.substitute (renameVariableWord e f).word ρ := by
  obtain ⟨ρ, hρ⟩ := h
  refine ⟨fun v => Sum.map e id (ρ v), ?_⟩
  change (fun s => Sum.map e id (g.word s)) = _
  rw [hρ]
  exact map_substitute e f.word ρ

/-- Syntactic refinement transports in both directions for every alphabet. -/
theorem syntacticRefines_rename_iff {b n k m : Nat} {α β : Type*}
    (e : α ≃ β) (g : Word b n k α) (f : Word b n m α) :
    KVariableWord.SyntacticRefines (renameWord e g) (renameWord e f) ↔
      KVariableWord.SyntacticRefines g f := by
  constructor
  · intro h
    have hback := rename_substitution e.symm
      (renameVariableWord e f.toVariableWord)
      (renameVariableWord e g.toVariableWord) h
    simpa only [KVariableWord.SyntacticRefines, renameVariableWord, map_inverse]
      using hback
  · exact rename_substitution e f.toVariableWord g.toVariableWord

/-- Both the whole-tree containment and uniform-substitution clauses survive. -/
theorem starredBelow_rename_iff {b n l m : Nat} {α β : Type*}
    (e : α ≃ β) (U : Starred b n l α) (f : Word b n m α) :
    StarredBelow (renameStarred e U) (renameWord e f) ↔ StarredBelow U f := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have hback := rename_substitution e.symm
      (renameVariableWord e f.toVariableWord)
      (renameVariableWord e U.word) h.2
    simpa only [renameVariableWord, map_inverse] using hback
  · intro h
    exact ⟨h.1, rename_substitution e f.toVariableWord U.word h.2⟩

/-- The actual intrinsic boundary selector ignores alphabet names, at all l. -/
theorem canonicalPoint_rename {b n l : Nat} {α β : Type*}
    (e : α ≃ β) (U : Starred b n l α)
    (a : CanonicalTheoremSpec.Boundary b l) :
    ForwardSemiCompleteSimplicity.canonicalPoint (renameStarred e U) a =
      ForwardSemiCompleteSimplicity.canonicalPoint U a := by
  have hroot : ForwardSemiCompleteZeroRoot.starredRootAll (renameStarred e U) =
      ForwardSemiCompleteZeroRoot.starredRootAll U := by
    apply isPrefix_antisymm
    · exact ForwardSemiCompleteZeroRoot.starredRootAll_prefix
        (renameStarred e U) _
        (ForwardSemiCompleteZeroRoot.starredRootAll_mem U)
    · exact ForwardSemiCompleteZeroRoot.starredRootAll_prefix U _
        (ForwardSemiCompleteZeroRoot.starredRootAll_mem (renameStarred e U))
  unfold ForwardSemiCompleteSimplicity.canonicalPoint
    ForwardSemiCompleteZeroRoot.canonicalWalkAll
  rw [hroot]
  rfl

/-- Canonical simplicity pulls back through alphabet and colour renaming.
The same selected boundary set is retained, including at zero interior. -/
theorem simpleWith_pullback {b n l : Nat} {α β γ δ : Type*}
    (e : α ≃ β) (h : δ → γ)
    (B₂ : Set (CanonicalTheoremSpec.Boundary b l))
    (c : StarredObservation b n β → δ)
    (hc : CanonicalTheoremSpec.SimpleWith B₂ c) :
    CanonicalTheoremSpec.SimpleWith B₂
      (fun O => h (c (renameStarredObservation e O))) := by
  intro U V hInt hPoints hWord
  apply congrArg h
  rw [← starredObserve_rename e U, ← starredObserve_rename e V]
  apply hc (renameStarred e U) (renameStarred e V) hInt
  · intro a ha
    simpa only [canonicalPoint_rename] using hPoints a ha
  · intro s hs
    change CutPreservation.underlyingSymbol (renameVariableWord e U.word) s =
      CutPreservation.underlyingSymbol (renameVariableWord e V.word) s
    rw [underlyingSymbol_rename, underlyingSymbol_rename]
    apply congrArg (Sum.map e id)
    exact hWord s (by simpa only [canonicalPoint_rename] using hs)

private theorem treeRamseyAt_transport {b n k m : Nat} {α β γ δ : Type*}
    (e : α ≃ β) (d : γ ≃ δ)
    (h : TreeRamseyAt b n k m α γ) : TreeRamseyAt b n k m β δ := by
  intro c
  obtain ⟨f, hf⟩ := h (fun w => d.symm (c (renameWordObservation e w)))
  refine ⟨renameWord e f, ?_⟩
  intro g g' hg hg'
  have hgback : KVariableWord.SyntacticRefines (renameWord e.symm g) f := by
    have hren := (syntacticRefines_rename_iff e.symm g (renameWord e f)).2 hg
    simpa only [renameWord_inverse] using hren
  have hg'back : KVariableWord.SyntacticRefines (renameWord e.symm g') f := by
    have hren := (syntacticRefines_rename_iff e.symm g' (renameWord e f)).2 hg'
    simpa only [renameWord_inverse] using hren
  have hmono := hf (renameWord e.symm g) (renameWord e.symm g') hgback hg'back
  apply d.symm.injective
  simpa only [wordObserve_rename,
    renameWordObservation_inverse'] using hmono

/-- The corrected complete-word Ramsey target is invariant under alphabet
and colour equivalences.  This is a transport theorem, not existence. -/
theorem treeRamseyAt_equiv {b n k m : Nat} {α β γ δ : Type*}
    (e : α ≃ β) (d : γ ≃ δ) :
    TreeRamseyAt b n k m α γ ↔ TreeRamseyAt b n k m β δ :=
  ⟨treeRamseyAt_transport e d, treeRamseyAt_transport e.symm d.symm⟩

private theorem canonicalRamseyAt_transport {b n l m : Nat} {α β γ δ : Type*}
    (e : α ≃ β) (d : γ ≃ δ)
    (h : CanonicalTheoremSpec.RamseyAt b n l m α γ) :
    CanonicalTheoremSpec.RamseyAt b n l m β δ := by
  intro c hc
  obtain ⟨B₂, hB₂⟩ := hc
  obtain ⟨f, hf⟩ := h
    (fun O => d.symm (c (renameStarredObservation e O)))
    ⟨B₂, simpleWith_pullback e d.symm B₂ c hB₂⟩
  refine ⟨renameWord e f, ?_⟩
  intro U V hU hV
  have hUback : StarredBelow (renameStarred e.symm U) f := by
    have hren := (starredBelow_rename_iff e.symm U (renameWord e f)).2 hU
    simpa only [renameWord_inverse] using hren
  have hVback : StarredBelow (renameStarred e.symm V) f := by
    have hren := (starredBelow_rename_iff e.symm V (renameWord e f)).2 hV
    simpa only [renameWord_inverse] using hren
  have hmono := hf (renameStarred e.symm U) (renameStarred e.symm V) hUback hVback
  apply d.symm.injective
  simpa only [starredObserve_rename,
    renameStarredObservation_inverse'] using hmono

/-- The canonical-selector starred Ramsey target transports with the actual
simplicity predicate and all nonnegative interior counts. -/
theorem canonicalRamseyAt_equiv {b n l m : Nat} {α β γ δ : Type*}
    (e : α ≃ β) (d : γ ≃ δ) :
    CanonicalTheoremSpec.RamseyAt b n l m α γ ↔
      CanonicalTheoremSpec.RamseyAt b n l m β δ :=
  ⟨canonicalRamseyAt_transport e d, canonicalRamseyAt_transport e.symm d.symm⟩

/-- The same complete-word threshold works after renaming; no loss is added. -/
theorem treeBound_equiv {b k m N : Nat} {α β γ δ : Type*}
    (e : α ≃ β) (d : γ ≃ δ) :
    EventualBound (fun n => TreeRamseyAt b n k m α γ) N ↔
      EventualBound (fun n => TreeRamseyAt b n k m β δ) N := by
  constructor
  · intro h
    exact ⟨h.1, fun n hn => (treeRamseyAt_equiv e d).1 (h.2 n hn)⟩
  · intro h
    exact ⟨h.1, fun n hn => (treeRamseyAt_equiv e d).2 (h.2 n hn)⟩

/-- The same canonical-starred threshold works after renaming. -/
theorem canonicalBound_equiv {b l m N : Nat} {α β γ δ : Type*}
    (e : α ≃ β) (d : γ ≃ δ) :
    EventualBound (fun n => CanonicalTheoremSpec.RamseyAt b n l m α γ) N ↔
      EventualBound (fun n => CanonicalTheoremSpec.RamseyAt b n l m β δ) N := by
  constructor
  · intro h
    exact ⟨h.1, fun n hn => (canonicalRamseyAt_equiv e d).1 (h.2 n hn)⟩
  · intro h
    exact ⟨h.1, fun n hn => (canonicalRamseyAt_equiv e d).2 (h.2 n hn)⟩

/-- The canonical `Fin` complete-word bound is exactly the arbitrary finite
alphabet/colour bound with those cardinalities, at the same threshold. -/
theorem tgrBound_iff_finite {b k m N : Nat} (α γ : Type*)
    [Fintype α] [Fintype γ] :
    TGRBound b (Fintype.card α) k m (Fintype.card γ) N ↔
      EventualBound (fun n => TreeRamseyAt b n k m α γ) N :=
  treeBound_equiv (Fintype.equivFin α).symm (Fintype.equivFin γ).symm

/-- The canonical `Fin` partial-tree bound has the same finite-alphabet
interpretation, with the canonical boundary selector unchanged. -/
theorem canonicalBound_iff_finite {b l m N : Nat} (α γ : Type*)
    [Fintype α] [Fintype γ] :
    CanonicalTheoremSpec.Bound b (Fintype.card α) l m (Fintype.card γ) N ↔
      EventualBound (fun n => CanonicalTheoremSpec.RamseyAt b n l m α γ) N :=
  canonicalBound_equiv (Fintype.equivFin α).symm (Fintype.equivFin γ).symm

/-- Once the corrected canonical theorem is proved, its full finite-alphabet
statement follows, including singleton alphabets.  Existence remains an input. -/
theorem correctedTheorem3_finite
    (h : CorrectedTheoremSpec.CorrectedTheorem3)
    (b k m : Nat) (hb : 0 < b) (hk : 0 < k) (hm : 0 < m)
    (α γ : Type*) [Fintype α] [Fintype γ] [Nonempty α] [Nonempty γ] :
    ∃ N, EventualBound (fun n => TreeRamseyAt b n k m α γ) N := by
  obtain ⟨N, hN⟩ := h b (Fintype.card α) k m (Fintype.card γ)
    hb Fintype.card_pos hk hm Fintype.card_pos
  exact ⟨N, (tgrBound_iff_finite α γ).1 hN⟩

/-- The corrected canonical-selector Theorem 25 similarly gives every
nonempty finite alphabet and finite colour set, without changing its bound. -/
theorem correctedTheorem25_finite
    (h : CanonicalTheoremSpec.CorrectedTheorem25)
    (b l m : Nat) (hb : 0 < b) (hm : 0 < m)
    (α γ : Type*) [Fintype α] [Fintype γ] [Nonempty α] [Nonempty γ] :
    ∃ N, EventualBound (fun n => CanonicalTheoremSpec.RamseyAt b n l m α γ) N := by
  obtain ⟨N, hN⟩ := h b (Fintype.card α) l m (Fintype.card γ)
    hb Fintype.card_pos hm Fintype.card_pos
  exact ⟨N, (canonicalBound_iff_finite α γ).1 hN⟩

end DualTree.TheoremAlphabetTransport
