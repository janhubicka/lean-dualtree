import DualTree.ForwardSignatureBoundary
import DualTree.CanonicalForwardAuxIso

/-!
# The strict corrected signature domain uniquely determines its cut

Definition 26 restricts the old source variable word to the
STRICT initial segment of the homogeneous tree before the last
interior cut. The cut is omitted from the restricted word, but
the DOMAIN of that partial word uniquely identifies it.

The corrected length-first forward auxiliary order is linear.
If two distinct cuts have the same strict-before-cut domain,
compare the cuts. The smaller cut itself belongs to the larger
domain but not its own smaller domain, a contradiction.

This is a useful source-facing rigidity lemma: the paper's
literal fixed signature carries both a restricted WORD and
its strict initial-segment domain. Agreement of those domains
forces equality of the last interior cut, so a common-cut
hypothesis need not be postulated once signature equality is
represented with its actual domain.

The statement is proved both for raw finite nodes and for
the bounded homogeneous-word index type used by the actual
starred variable words; the bounded proof explicitly checks
that each cut itself lies in the same ambient index universe.
No printed reverse-order equivalence is asserted.
-/

namespace DualTree.ForwardSignatureCutDomainRigidity

/-- The full strict forward-auxiliary initial segment before
a finite node cut, viewed as a set of raw tree nodes. -/
def strictDomain {b : Nat} (cut : Node b) : Set (Node b) :=
  {s | ForwardSignatureBoundary.BeforeCut cut s}

/-- Identical strict initial segments of the corrected forward
linear order force the same cut. -/
theorem cut_eq_of_strictDomain_eq
    {b : Nat} (u v : Node b)
    (heq : strictDomain u = strictDomain v) :
    u = v := by
  by_contra hne
  rcases CanonicalForwardAuxIso.forwardAux_total u v with huv | hvu
  · have hv : ForwardSignatureBoundary.BeforeCut v u :=
      ⟨huv,hne⟩
    have hu : ForwardSignatureBoundary.BeforeCut u u := by
      have hmem : u ∈ strictDomain v := hv
      rw [← heq] at hmem
      exact hmem
    exact hu.2 rfl
  · have hu : ForwardSignatureBoundary.BeforeCut u v :=
      ⟨hvu,(Ne.symm hne)⟩
    have hv : ForwardSignatureBoundary.BeforeCut v v := by
      have hmem : v ∈ strictDomain u := hu
      rw [heq] at hmem
      exact hmem
    exact hv.2 rfl

/-- More specifically, two strict prefix domains agree
pointwise on every raw tree node only if their cuts agree. -/
theorem cut_eq_of_all_beforeCut_iff
    {b : Nat} (u v : Node b)
    (h :
      ∀ s : Node b,
        ForwardSignatureBoundary.BeforeCut u s ↔
        ForwardSignatureBoundary.BeforeCut v s) :
    u = v := by
  apply cut_eq_of_strictDomain_eq u v
  ext s
  exact h s

/-- The TRUE bounded ambient indices suffice to recognize the
cut: if both cuts are bounded by n, their strict prefix domains
agree on all bounded words only when the cuts are identical. -/
theorem bounded_cut_eq_of_beforeCut_iff
    {b n : Nat} (u v : BoundedNode b n)
    (h :
      ∀ s : BoundedNode b n,
        ForwardSignatureBoundary.BeforeCut u.1 s.1 ↔
        ForwardSignatureBoundary.BeforeCut v.1 s.1) :
    u = v := by
  apply Subtype.ext
  by_contra hne
  rcases CanonicalForwardAuxIso.forwardAux_total u.1 v.1 with huv | hvu
  · have hv : ForwardSignatureBoundary.BeforeCut v.1 u.1 :=
      ⟨huv,hne⟩
    have hu : ForwardSignatureBoundary.BeforeCut u.1 u.1 :=
      (h u).2 hv
    exact hu.2 rfl
  · have hu : ForwardSignatureBoundary.BeforeCut u.1 v.1 :=
      ⟨hvu,(Ne.symm hne)⟩
    have hv : ForwardSignatureBoundary.BeforeCut v.1 v.1 :=
      (h v).1 hu
    exact hv.2 rfl

end DualTree.ForwardSignatureCutDomainRigidity
