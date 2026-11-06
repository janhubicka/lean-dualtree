import DualTree.UpLeafMixedWord

/-!
# A concrete D₀/D₁/D₂ mixed fixture

The three coordinates have distinct root lengths 0, 1 and 2 inside the
ambient tree of height 3. The middle coordinate carries exactly `b` real
level-3 leaves. Every root letter and every middle-coordinate direction
occurs independently in the actual span.
-/

namespace DualTree.UpLeafExamples

open DualTree.MixedProduct
open DualTree.UpLeafMixedWord

def threeKind (i : Fin 3) : CoordKind :=
  if i = 0 then .plain else if i = 1 then .up else .bullet

def upIndex : UpIndex threeKind := ⟨1, by decide⟩

def bulletIndex : BulletIndex threeKind := ⟨2, by decide⟩

def roots {b : Nat} (hb : 0 < b) (i : Fin 3) : BoundedNode b 3 :=
  ⟨List.replicate i.val ⟨0, hb⟩, by simpa [InHomTree] using i.isLt⟩

theorem roots_length {b : Nat} (hb : 0 < b) (i : Fin 3) :
    (roots hb i).1.length = i.val := by simp [roots]

theorem roots_ordered {b : Nat} (hb : 0 < b) :
    ∀ i j : Fin 3, i < j → (roots hb i).1.length ≤ (roots hb j).1.length := by
  intro i j hij
  simpa only [roots_length] using Nat.le_of_lt hij

noncomputable def threeWord {b : Nat} {α : Type*} (hb : 0 < b) (a : α) :
    MixedProduct.VariableWord b 3 3 1 α SkewTree.forwardAuxB threeKind :=
  mixedWord hb threeKind (roots hb) (roots_ordered hb) a

theorem threeWord_span_nonempty {b : Nat} {α : Type*}
    (hb : 0 < b) (a : α) : (threeWord hb a).span.Nonempty :=
  mixedWord_span_nonempty hb threeKind (roots hb) (roots_ordered hb) a

theorem threeWord_upLeaves_card {b : Nat} {α : Type*}
    (hb : 0 < b) (a : α) : ((threeWord hb a).upLeaves upIndex).length = b := by
  simpa using (threeWord hb a).upLeaves_card upIndex

/-- Each branch produces a genuine span point with the SAME independently
specified root letters. This rules out treating the up coordinate as empty. -/
theorem threeWord_direction_mem_span {b : Nat} {α : Type*}
    (hb : 0 < b) (fallback : α) (a : Fin 3 → α) (i : Fin b) :
    parameterElement hb threeKind (roots hb) fallback a (fun _ => i) ∈
      (threeWord hb fallback).span :=
  parameterElement_mem_span hb threeKind (roots hb) (roots_ordered hb)
    fallback a (fun _ => i)

/-- Distinct actual branch choices remain distinct mixed-span points. -/
theorem threeWord_directions_distinct {b : Nat} {α : Type*}
    (hb : 0 < b) (fallback : α) (a : Fin 3 → α)
    {i j : Fin b} (hij : i ≠ j) :
    parameterElement hb threeKind (roots hb) fallback a (fun _ => i) ≠
      parameterElement hb threeKind (roots hb) fallback a (fun _ => j) := by
  intro h
  have hpair := parameterElement_injective hb threeKind (roots hb) fallback h
  have hdir := congrArg Prod.snd hpair
  exact hij (congrFun hdir upIndex)

end DualTree.UpLeafExamples
