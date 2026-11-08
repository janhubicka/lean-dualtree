import DualTree.HigherRamseyFlat
import DualTree.NodeOrder

/-!
# Track C: actual depth-N cone addresses in the finite two-stage Ramsey step

Using an opaque ordinal \`Fin (b^N)\` for depth-N cone indices postpones a
substantial geometric correspondence. Here an address is the actual finite
function \`Fin N → Fin b\`, i.e. its N branch digits. \`List.ofFn\` interprets
the address as a tree node of length N. We prove the selected branch indices
are genuinely distinct and the two-stage Hales--Jewett theorem already works
with this typed address space.

This is still a *flat* Ramsey input, not an embedding of the resulting word
into a complete skew variable-word support. The support/word transport remains
the next explicit Track C obligation.
-/

namespace DualTree.HigherConeAddresses

/-- Actual addresses of the b-branching tree at depth N. -/
abbrev Address (b N : Nat) := Fin N → Fin b

/-- View an address as its sequence of branch digits. -/
def addressNode {b N : Nat} (a : Address b N) : Node b :=
  List.ofFn a

theorem addressNode_length {b N : Nat} (a : Address b N) :
    (addressNode a).length = N := by
  simp [addressNode]

/-- A distinguished address whose r-th digit is direction i and whose
other digits are zero, for any actual branching b>0. -/
def branchAddress {b N : Nat} (hb : 0 < b)
    (r : Fin N) (i : Fin b) : Address b N :=
  fun j => if j = r then i else ⟨0, hb⟩

theorem branchAddress_at_root {b N : Nat} (hb : 0 < b)
    (r : Fin N) (i : Fin b) :
    branchAddress hb r i r = i := by
  simp [branchAddress]

theorem branchAddress_elsewhere {b N : Nat} (hb : 0 < b)
    (r : Fin N) (i : Fin b) (j : Fin N) (h : j ≠ r) :
    branchAddress hb r i j = ⟨0, hb⟩ := by
  simp [branchAddress, h]

/-- Choosing different ambient directions yields genuinely different
length-N cone addresses. This is the noncollapse needed for b children. -/
theorem branchAddress_injective {b N : Nat} (hb : 0 < b)
    (r : Fin N) :
    Function.Injective (branchAddress hb r) := by
  intro i j hij
  have hroot := congrFun hij r
  simpa [branchAddress] using hroot

/-- The chosen b addresses are pairwise distinct as a concrete list, not
merely a function family without a cardinality guarantee. -/
theorem branchAddresses_nodup {b N : Nat} (hb : 0 < b)
    (r : Fin N) :
    (List.ofFn (branchAddress hb r)).Nodup := by
  exact List.nodup_ofFn.mpr (branchAddress_injective hb r)

/-- A genuinely unconditional finite Ramsey input indexed by ALL actual
depth-N addresses, not by a postulated equivalence \`Fin (b^N)\`.

The root and cone variables may be assigned independently at every vector
coordinate and every address, and both words are proper. The cone line is
selected uniformly over all root-band words before the root line is chosen. -/
theorem exists_uniform_root_and_address_cones
    (b : Nat) (β γ : Type*) [Finite β] [Finite γ] (d : Nat) :
    ∃ N M : Nat,
      ∀ C : (Fin N → Fin d → β) →
          (Fin M → Fin d → Address b N → β) → γ,
        ∃ root : Fin N → Sum (Fin d → β) (Fin 1),
          (∀ v : Fin 1, ∃ j : Fin N, root j = Sum.inr v) ∧
        ∃ cone : Fin M → Sum (Fin d → Address b N → β) (Fin 1),
          (∀ v : Fin 1, ∃ j : Fin M, cone j = Sum.inr v) ∧
        ∃ col : γ,
          ∀ σ : Fin 1 → Fin d → β,
            ∀ τ : Fin 1 → Fin d → Address b N → β,
              C (SpanAudit.eval root σ) (SpanAudit.eval cone τ) = col := by
  obtain ⟨N, hRoot⟩ :=
    FlatHalesJewett.exists_monochromatic_flat_word (Fin d → β) γ 1
  obtain ⟨M, hCone⟩ :=
    ParameterHalesJewett.exists_uniform_flat_word
      (Fin d → Address b N → β) (Fin N → Fin d → β) γ 1
  refine ⟨N, M, ?_⟩
  intro C
  let coneColor :
      (Fin M → Fin d → Address b N → β) →
        (Fin N → Fin d → β) → γ :=
    fun y x => C x y
  obtain ⟨cone, hConeProper, F, hUniform⟩ := hCone coneColor
  obtain ⟨root, hRootProper, col, hMono⟩ := hRoot F
  refine ⟨root, hRootProper, cone, hConeProper, col, ?_⟩
  intro σ τ
  exact (hUniform τ (SpanAudit.eval root σ)).trans (hMono σ)

end DualTree.HigherConeAddresses
