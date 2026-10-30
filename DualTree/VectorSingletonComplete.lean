import DualTree.VectorSkew

/-!
# Synchronized singleton supports are genuinely vector 1-complete skew

For intrinsic height one, every support component may use the SAME
single bounded tree node. Componentwise 1-completeness follows from
the singleton skew convention. The same-level ambient-length
ordering is automatic because the chosen nodes coincide, and the
successive-level clause is empty at height one.

This is a verified geometric bridge useful for lifting a
synchronized product-alphabet Hales–Jewett line to a true vector
of tree-variable words. It does NOT give higher-height
complete-skew vector supports or any D₁/D₂ mixed markers.
-/

namespace DualTree.VectorSkew

/-- A vector of identical singleton tree supports satisfies the
FULL vector 1-complete-skew predicate for any number of
coordinates and either chosen auxiliary order. -/
theorem identical_singletons_vectorComplete_one
    {b d : Nat}
    (aux : Node b → Node b → Bool)
    (s : Node b) :
    vectorCompleteB aux 1 (fun _ : Fin d => [s]) = true := by
  simp [vectorCompleteB, sameLevelOrderedB,
    successiveLevelsSeparatedB, levelNodes,
    SkewTree.singleton_complete_oneB,
    SkewTree.heightAt, SkewTree.preds, SkewTree.strictPrefixB]

end DualTree.VectorSkew
