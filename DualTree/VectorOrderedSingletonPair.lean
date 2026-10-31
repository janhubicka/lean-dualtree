import DualTree.VectorSingletonComplete

/-!
# Ordered, DISTINCT singleton roots in a genuine vector 1-complete skew tree

The synchronized vector Hales–Jewett theorem used identical support
roots in all components. That is not sufficient for the mixed D₀/D₂
c-good case: an adversarial colouring can read the D₀ letter at
the marked D₂ root, making the colours vary when both independent
variables share that point.

The first genuinely mixed construction must choose separate D₀ and
D₂ variable-root positions. At intrinsic height one, the entire
cross-coordinate vector-skew requirement for two singleton supports
reduces to the weak ambient-length ordering of those roots.

The proof here is *geometric*: it verifies the actual executable
VectorSkew.vectorCompleteB definition and not merely the separate
KVariableWord component completeness.
-/

namespace DualTree.VectorSkew

/-- Two singleton supports in the fixed coordinate order
D₀, D₂. Their positions need not be equal or comparable
under the tree-prefix order. -/
def orderedSingletonPair {b : Nat}
    (s t : Node b) : Fin 2 → List (Node b) :=
  fun i => if i = 0 then [s] else [t]

/-- The zero-th coordinate and first coordinate have their
specified singleton supports. -/
theorem orderedSingletonPair_zero {b : Nat} (s t : Node b) :
    orderedSingletonPair s t 0 = [s] := by
  simp [orderedSingletonPair]

theorem orderedSingletonPair_one {b : Nat} (s t : Node b) :
    orderedSingletonPair s t 1 = [t] := by
  simp [orderedSingletonPair]

/-- At intrinsic height one, the SAME-LEVEL ordering is
exactly the ordering of the two singleton ambient lengths.
Both nodes have intrinsic height zero in their own support. -/
theorem orderedSingletonPair_sameLevel
    {b : Nat} (s t : Node b)
    (hlen : s.length ≤ t.length) :
    sameLevelOrderedB (orderedSingletonPair s t) 1 = true := by
  simp [sameLevelOrderedB, orderedSingletonPair,
    levelNodes, SkewTree.heightAt, SkewTree.preds,
    SkewTree.strictPrefixB, SkewTree.allFin, hlen]

/-- The source-facing vector 1-complete-skew condition
for a pair of singleton support roots, with the exact
weak ambient-length requirement from clause (ii).
No equality of the two roots is assumed. -/
theorem orderedSingletonPair_vectorComplete_one
    {b : Nat}
    (aux : Node b → Node b → Bool)
    (s t : Node b)
    (hlen : s.length ≤ t.length) :
    vectorCompleteB aux 1 (orderedSingletonPair s t) = true := by
  have hfirst : SkewTree.completeB aux 1 [s] = true :=
    SkewTree.singleton_complete_oneB aux s
  have hsecond : SkewTree.completeB aux 1 [t] = true :=
    SkewTree.singleton_complete_oneB aux t
  have hsame := orderedSingletonPair_sameLevel s t hlen
  simp [vectorCompleteB, orderedSingletonPair, SkewTree.allFin,
    hfirst, hsecond, hsame, successiveLevelsSeparatedB,
    sameLevelOrderedB, levelNodes, SkewTree.heightAt,
    SkewTree.preds, SkewTree.strictPrefixB, hlen]

end DualTree.VectorSkew
