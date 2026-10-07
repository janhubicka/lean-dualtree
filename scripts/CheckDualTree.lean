import DualTree

/-!
Transitive axiom audit for the first source-facing validation facts.
-/

#print axioms DualTree.isPrefix_refl
#print axioms DualTree.isPrefix_trans
#print axioms DualTree.OrderAudit.canonical_order_counterexample
#print axioms DualTree.Insensitivity.constantOn_union_of_overlap
#print axioms DualTree.SpanAudit.singleton_span_subset
#print axioms DualTree.BinarySkewAudit.remark2_witness_is_semicomplete_printed
#print axioms DualTree.BinarySkewAudit.remark2_interior_not_skew_printed
#print axioms DualTree.Remark1Audit.forwardS_is_skew
#print axioms DualTree.Remark1Audit.forwardTprime_is_skew
#print axioms DualTree.Remark1Audit.no_forward_complete_extension

#print axioms DualTree.SpanAudit.eval_substitute
#print axioms DualTree.SpanAudit.span_substitute_subset
#print axioms DualTree.SpanAudit.symbol_eq_of_all_evals
#print axioms DualTree.SpanAudit.constant_preserved_of_span_subset
#print axioms DualTree.SpanAudit.fibre_uniform_of_span_subset
#print axioms DualTree.SpanAudit.span_subset_iff_substitution
#print axioms DualTree.SkewTree.singleton_skewB
#print axioms DualTree.SkewTree.singleton_complete_oneB

#print axioms DualTree.isPrefix_antisymm
#print axioms DualTree.VariableWord.every_var_occurs
#print axioms DualTree.VariableWord.span_subset_iff_substitution
#print axioms DualTree.VariableWord.support_subset_of_span_subset

#print axioms DualTree.StarInsensitivity.starRelated_iff
#print axioms DualTree.StarInsensitivity.singleton_insensitive
#print axioms DualTree.StarInsensitivity.disjoint_union_failure
#print axioms DualTree.StarInsensitivity.starInsensitive_union_of_overlap
