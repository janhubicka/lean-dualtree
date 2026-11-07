import DualTree.Lemma27CanonicalPointColor

/-!
# A total residual colour on the selected boundary tuples

Once the local Q step makes a fixed signature fibre depend only on its
canonical B₂ points, the remaining colour is an actual total function of
those points.  It is defined by choosing an eligible representative when
one exists and using a fallback colour on all other tuples.  The proved
point-canonical property makes the choice exact on every eligible object.

This residual colour is chosen after the containing word and signature
are fixed.  Homogenizing it on the tuples realized inside a further
syntactic refinement makes the entire corresponding signature fibre
monochromatic.  The tuples themselves need not be equal.  Constructing
such a refinement, with the required preservation and height bounds,
remains a separate Ramsey input.
-/

namespace DualTree.Lemma27BoundaryFactor

open CorrectedTheoremSpec
open Lemma27CanonicalPointColor

/-- The surviving data consist of one actual node for each selected
intrinsic model-boundary address. -/
abbrev PointTuple {b l : Nat}
    (B2 : Set (CanonicalTheoremSpec.Boundary b l)) :=
  B2 → Node b

/-- The selected boundary tuple of a genuine starred object. -/
noncomputable def pointTuple
    {b n l : Nat} {α : Type*}
    (B2 : Set (CanonicalTheoremSpec.Boundary b l))
    (O : Starred b n l α) : PointTuple B2 :=
  fun a => ForwardSemiCompleteSimplicity.canonicalPoint O a.1

/-- Only tuples realized in the prescribed signature fibre of the actual
word participate in the remaining homogenization problem. -/
def realizedTuples
    {b n l k : Nat} {α Sig : Type*}
    (signature : Starred b n l α → Sig)
    (B2 : Set (CanonicalTheoremSpec.Boundary b l))
    (f : Word b n k α) (s : Sig) : Set (PointTuple B2) :=
  {p | ∃ O : Starred b n l α,
    StarredBelow O f ∧ signature O = s ∧ pointTuple B2 O = p}

/-- A total colour on all boundary tuples, chosen after `f` and `s`.
The fallback is used precisely when no eligible object realizes a tuple. -/
noncomputable def residualColor
    {b n l k : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (B2 : Set (CanonicalTheoremSpec.Boundary b l))
    (color : Starred b n l α → γ)
    (f : Word b n k α) (s : Sig) (fallback : γ)
    (p : PointTuple B2) : γ := by
  classical
  exact if h : ∃ O : Starred b n l α,
      StarredBelow O f ∧ signature O = s ∧ pointTuple B2 O = p then
    color (Classical.choose h)
  else fallback

/-- Point canonization makes the total residual colour exact on every
eligible object of the fixed signature fibre. -/
theorem residualColor_exact
    {b n l k : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (B2 : Set (CanonicalTheoremSpec.Boundary b l))
    (color : Starred b n l α → γ)
    (f : Word b n k α) (s : Sig) (fallback : γ)
    (hcanonical : FibrePointCanonical signature B2 color f s)
    (O : Starred b n l α) (hO : StarredBelow O f)
    (hs : signature O = s) :
    residualColor signature B2 color f s fallback (pointTuple B2 O) =
      color O := by
  classical
  have h : ∃ U : Starred b n l α,
      StarredBelow U f ∧ signature U = s ∧
        pointTuple B2 U = pointTuple B2 O := ⟨O, hO, hs, rfl⟩
  simp only [residualColor, dif_pos h]
  apply hcanonical (Classical.choose h) O
    (Classical.choose_spec h).1 hO (Classical.choose_spec h).2.1 hs
  intro a ha
  exact congrFun (Classical.choose_spec h).2.2 (⟨a, ha⟩ : B2)

/-- A fixed signature fibre is point-canonical exactly when its colour
factors through the selected tuple by a total function.  The fallback
also covers unrealized tuples and the possibility of an empty fibre. -/
theorem fibrePointCanonical_iff_exists_residualColor
    {b n l k : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (B2 : Set (CanonicalTheoremSpec.Boundary b l))
    (color : Starred b n l α → γ)
    (f : Word b n k α) (s : Sig) (fallback : γ) :
    FibrePointCanonical signature B2 color f s ↔
      ∃ residual : PointTuple B2 → γ,
        ∀ O : Starred b n l α, StarredBelow O f → signature O = s →
          residual (pointTuple B2 O) = color O := by
  constructor
  · intro hcanonical
    exact ⟨residualColor signature B2 color f s fallback,
      residualColor_exact signature B2 color f s fallback hcanonical⟩
  · rintro ⟨residual, hexact⟩
    intro U V hU hV hsU hsV hpoints
    have htuple : pointTuple B2 U = pointTuple B2 V := by
      funext a
      exact hpoints a.1 a.2
    exact (hexact U hU hsU).symm.trans
      ((congrArg residual htuple).trans (hexact V hV hsV))

/-- Homogeneity of the residual colour on the tuples actually realized
inside a further syntactic refinement canonizes the whole signature fibre.
This requires equal residual colours, not equal selected boundary points. -/
theorem fibreMonochromatic_of_residualColor_homogeneous
    {b n l k k' : Nat} {α γ Sig : Type*}
    (signature : Starred b n l α → Sig)
    (B2 : Set (CanonicalTheoremSpec.Boundary b l))
    (color : Starred b n l α → γ)
    (f : Word b n k α) (g : Word b n k' α)
    (s : Sig) (fallback : γ)
    (hgf : KVariableWord.SyntacticRefines g f)
    (hcanonical : FibrePointCanonical signature B2 color f s)
    (hmono : ∀ p q : PointTuple B2,
      p ∈ realizedTuples signature B2 g s →
      q ∈ realizedTuples signature B2 g s →
      residualColor signature B2 color f s fallback p =
        residualColor signature B2 color f s fallback q) :
    Lemma28.FibreMonochromatic signature color g s := by
  intro U V hU hV hsU hsV
  have hUcolor := residualColor_exact signature B2 color f s fallback
    hcanonical U (starredBelow_of_syntacticRefines hgf hU) hsU
  have hVcolor := residualColor_exact signature B2 color f s fallback
    hcanonical V (starredBelow_of_syntacticRefines hgf hV) hsV
  have hsame := hmono (pointTuple B2 U) (pointTuple B2 V)
    ⟨U, hU, hsU, rfl⟩ ⟨V, hV, hsV, rfl⟩
  exact hUcolor.symm.trans (hsame.trans hVcolor)

end DualTree.Lemma27BoundaryFactor
