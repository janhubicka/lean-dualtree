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

#print axioms DualTree.Theorem3Audit.root_support_complete
#print axioms DualTree.Theorem3Audit.left_support_complete
#print axioms DualTree.Theorem3Audit.supports_differ
#print axioms DualTree.Theorem3Audit.unary_spans_equal
#print axioms DualTree.Theorem3Audit.two_colors_below_every_candidate

#print axioms DualTree.UnaryMainAudit.unary_refines_all
#print axioms DualTree.UnaryMainAudit.rootWord_complete
#print axioms DualTree.UnaryMainAudit.leftWord_complete
#print axioms DualTree.UnaryMainAudit.no_homogeneous_one
#print axioms DualTree.UnaryMainAudit.no_unary_eventual_bound

#print axioms DualTree.Corollary22Audit.color_is_smooth
#print axioms DualTree.Corollary22Audit.no_monochromatic_complete_candidate
#print axioms DualTree.Corollary22Audit.canonical_complete_one
#print axioms DualTree.Corollary22Audit.canonical_good_for_every_coloring

#print axioms DualTree.VariableWord.supportNodes_nodup
#print axioms DualTree.KVariableWord.refines_refl
#print axioms DualTree.KVariableWord.refines_trans
#print axioms DualTree.KVariableWord.refines_iff_syntactic
#print axioms DualTree.KVariableWord.support_subset_of_refines

#print axioms DualTree.KVariableWord.substitute_compose
#print axioms DualTree.KVariableWord.syntacticRefines_refl
#print axioms DualTree.KVariableWord.syntacticRefines_trans
#print axioms DualTree.KVariableWord.syntacticRefines_refines
#print axioms DualTree.KVariableWord.support_subset_of_syntacticRefines

#print axioms DualTree.VectorSkew.binaryHeightOneVector_complete
#print axioms DualTree.VectorSkew.binaryHeightOneVectorReversed_not_complete

#print axioms DualTree.MixedProduct.VariableWord.word_mem_of_mem_span
#print axioms DualTree.MixedProduct.VariableWord.upPoint_mem_of_mem_span
#print axioms DualTree.MixedProduct.VariableWord.bulletPoint_mem_support_of_mem_span

#print axioms DualTree.MixedProduct.good_iff_same_bulletRecord
#print axioms DualTree.MixedProduct.color_eq_of_good_of_same_record

#print axioms DualTree.GluingAudit.short_tail_stays_in_hom_tree
#print axioms DualTree.GluingAudit.exact_tail_leaves_hom_tree

#print axioms DualTree.MixedProduct.VariableWord.refines_refl
#print axioms DualTree.MixedProduct.VariableWord.refines_trans
#print axioms DualTree.MixedProduct.VariableWord.refines_of_syntactic_components
#print axioms DualTree.MixedProduct.good_of_refines
#print axioms DualTree.MixedProduct.good_of_syntactic_refinement

#print axioms DualTree.MixedProduct.noBulletIndex_elim
#print axioms DualTree.MixedProduct.good_iff_constant_on_span_of_noBullet
#print axioms DualTree.MixedProduct.good_of_constant_on_span_of_noBullet

#print axioms DualTree.MixedProduct.sameUpTrace_refl
#print axioms DualTree.MixedProduct.upCanonical_of_refines
#print axioms DualTree.MixedProduct.upCanonical_of_good_of_noBullet
#print axioms DualTree.MixedProduct.upCanonical_of_constant_on_span
