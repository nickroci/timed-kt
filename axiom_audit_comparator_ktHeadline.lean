import KtHeadline.Solution
-- Comparator trusted statement, comparator/config_ktHeadline.json. Run after
-- `lake build ComparatorKtHeadline`: `lake env lean axiom_audit_comparator_ktHeadline.lean`.
-- Expected: only propext / Classical.choice / Quot.sound (no sorryAx, no new axioms).
#print axioms KtHeadline.Solution.runEvalSpec
#print axioms KtHeadline.Solution.runDeterministic
#print axioms KtHeadline.Solution.compRunsComputable
#print axioms KtHeadline.Solution.compRunsUnique
#print axioms KtHeadline.Solution.conditioning
#print axioms KtHeadline.Solution.invarianceUniversal
#print axioms KtHeadline.Solution.invariance
#print axioms KtHeadline.Solution.lengthBound
#print axioms KtHeadline.Solution.triangle
#print axioms KtHeadline.Solution.symmetryEasy
#print axioms KtHeadline.Solution.fiveLeKtCond
#print axioms KtHeadline.Solution.ktNil
#print axioms KtHeadline.Solution.idTimedRealized
#print axioms KtHeadline.Solution.idTimedCondKt
#print axioms KtHeadline.Solution.fastTimedUnrealized
-- bridge
#print axioms KtHeadline.Solution.run_iff
#print axioms KtHeadline.Solution.compRuns_iff
#print axioms KtHeadline.Solution.Kt_cond_eq
#print axioms KtHeadline.Solution.KtU_cond_eq
#print axioms KtHeadline.Solution.condKt_eq
#print axioms KtHeadline.Solution.Realization.toLib
#print axioms KtHeadline.Solution.run_output_le
#print axioms KtHeadline.Solution.length_le_of_decode
