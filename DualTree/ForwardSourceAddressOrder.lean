import DualTree.ForwardSourceCanonicalAddresses
import DualTree.ForwardSourceInitialInterior
import DualTree.CanonicalForwardAux
import DualTree.CanonicalForwardAuxIso
import DualTree.ForwardOrderCompatibility

/-!
# Forward order of the actual semi-complete source's canonical addresses

The generic support-walk library gives lex monotonicity along any
two admissible direction sequences. Its complete-support order
theorem uses k-completeness only to supply admissibility and
rank identities.

For the ACTUAL semi-complete skew source the preceding module
already supplies those facts. We therefore transport the corrected
length-first forward auxiliary order directly from admissible
source addresses to their genuine source vertices, using:
* intrinsic rank = address length;
* skew clauses (ii) and (iii) for source ambient lengths;
* generic lex monotonicity of admissible support walks;
* injectivity of source walk to reflect the total order.

The last result identifies source interior addresses as exactly
the admissible addresses at or before the canonical address
of the last interior cut. This is a forward initial segment *of
the admissible address set*, NOT YET of the entire homogeneous
heap enumeration. Proving that all intermediate heap addresses
are admissible remains the next independent obligation.
-/

namespace DualTree.ForwardSourceAddressOrder

open ForwardSourceQTree
open ForwardSourceCanonicalAddresses

/-- The source vertex reached by an admissible direction word has
intrinsic height exactly the number of directions in that word. -/
theorem height_realize_eq_length
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u : SourceAddress c) :
    SkewTree.heightAt c.source.tree (realize c u).1 = u.1.length := by
  have hparts := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hparts
  have hskew := hparts.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  have hnd : c.source.tree.Nodup := by
    simpa using hskew.1
  have hwalk :=
    SupportReachability.walk_height_of_admissible
      c.source.tree hnd u.1 (ForwardQRooted.sourceRoot c)
      (ForwardQRooted.sourceRoot_mem c) u.2
  have hroot :
      SkewTree.heightAt c.source.tree
        (ForwardQRooted.sourceRoot c) = 0 :=
    ImmediateSupportHeight.heightAt_root_zero
      c.source.tree (ForwardQRooted.sourceRoot c)
      (fun v hv => ForwardQRooted.sourceRoot_prefix c v hv)
  change SkewTree.heightAt c.source.tree
      (CanonicalSupportWalk.walk c.source.tree
        (ForwardQRooted.sourceRoot c) u.1) = u.1.length
  rw [hwalk, hroot]
  omega

/-- Extract exactly the two source skew order hypotheses
from the ACTUAL semi-complete forward-skew source. -/
theorem source_numeric_order_clauses
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    SkewTree.condIIB c.source.tree = true ∧
      SkewTree.condIIIB c.source.tree = true := by
  have hparts := c.source.semi_complete
  simp only [SkewTree.semiCompleteB, Bool.and_eq_true] at hparts
  have hskew := hparts.1
  simp only [SkewTree.skewB, Bool.and_eq_true] at hskew
  have hrest := hskew.2
  simp [ForwardQRooted.source_nonsingleton c, Bool.and_eq_true] at hrest
  exact ⟨hrest.1.1.2, hrest.1.2⟩

/-- Corrected forward auxiliary comparisons between canonical
admissible direction words are preserved by the actual source
walk, despite arbitrarily stretched source edges. -/
theorem forwardAux_realize_mono
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : SourceAddress c)
    (huv : ForwardAux u.1 v.1) :
    ForwardAux (realize c u).1 (realize c v).1 := by
  obtain ⟨hII, hIII⟩ := source_numeric_order_clauses c
  rcases huv with hshort | ⟨heq, hlex⟩
  · have hrank :
        SkewTree.heightAt c.source.tree (realize c u).1 <
          SkewTree.heightAt c.source.tree (realize c v).1 := by
      rw [height_realize_eq_length c u,
        height_realize_eq_length c v]
      exact hshort
    exact ForwardOrderCompatibility.forwardAux_of_lower_height
      c.source.tree hIII (realize c u).2 (realize c v).2 hrank
  · have htargetLex :
        FinLexLE (realize c u).1 (realize c v).1 :=
      CanonicalForwardAux.walk_lex_of_admissible
        c.source.tree u.1 (ForwardQRooted.sourceRoot c)
        v.1 u.2 v.2 hlex
    have hequal :
        SkewTree.heightAt c.source.tree (realize c u).1 =
          SkewTree.heightAt c.source.tree (realize c v).1 := by
      rw [height_realize_eq_length c u,
        height_realize_eq_length c v]
      exact heq
    exact ForwardOrderCompatibility.forwardAux_of_equal_height_lex
      c.source.tree hII (realize c u).2 (realize c v).2
      hequal htargetLex

/-- The canonical admissible source walk reflects the forward
auxiliary order, by totality, monotonicity and its verified
injectivity. No reverse-lex order claim is made. -/
theorem forwardAux_realize_iff
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α)
    (u v : SourceAddress c) :
    ForwardAux u.1 v.1 ↔
      ForwardAux (realize c u).1 (realize c v).1 := by
  constructor
  · exact forwardAux_realize_mono c u v
  · intro himage
    rcases CanonicalForwardAuxIso.forwardAux_total
      u.1 v.1 with huv | hvu
    · exact huv
    · have hback := forwardAux_realize_mono c v u hvu
      have heqImage :
          (realize c u).1 = (realize c v).1 :=
        CanonicalForwardAuxIso.forwardAux_antisymm himage hback
      have hsource : u = v :=
        (realize_injective c) (Subtype.ext heqImage)
      subst v
      exact CanonicalForwardAuxIso.forwardAux_refl u.1

/-- A fixed canonical admissible source address for the final
interior cut, obtained by inverting the source-address bijection. -/
noncomputable def cutAddress
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) : SourceAddress c :=
  (sourceAddressEquiv c).symm
    ⟨c.cut, (List.mem_filter.mp c.hcut).1⟩

/-- The chosen final-cut address actually realizes the final
interior source vertex, not an arbitrary support node. -/
theorem realize_cutAddress
    {b n l k m : Nat} {α : Type*}
    (c : Frame b n l k m α) :
    (realize c (cutAddress c)).1 = c.cut := by
  have h :=
    (sourceAddressEquiv c).apply_symm_apply
      (⟨c.cut, (List.mem_filter.mp c.hcut).1⟩ :
        SourceVertex c)
  have hval := congrArg Subtype.val h
  simpa only [cutAddress,
    ForwardSourceCanonicalAddresses.sourceAddressEquiv_apply] using hval

/-- The original interior vertices correspond EXACTLY to
admissible canonical source addresses at or before the cut
address in repaired forward order. The source's l interior
addresses are thus initial among the *admissible* addresses.
The implication to the FULL first-l heap model is not
claimed by this theorem. -/
theorem address_interior_iff_forward_le_cut
    {b n l k m : Nat} {α : Type*}
    (hb : 0 < b)
    (c : Frame b n l k m α)
    (u : SourceAddress c) :
    (realize c u).1 ∈ SkewTree.interior c.source.tree ↔
      ForwardAux u.1 (cutAddress c).1 := by
  have hsource :=
    ForwardSourceInitialInterior.source_interior_iff_forward_le_cut
      hb c (realize c u).1 (realize c u).2
  have htransport :=
    forwardAux_realize_iff c u (cutAddress c)
  have hcutEq := realize_cutAddress c
  rw [hcutEq] at htransport
  exact hsource.trans htransport.symm

end DualTree.ForwardSourceAddressOrder
