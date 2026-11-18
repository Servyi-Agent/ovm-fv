/- The CI axiom gate: every load-bearing theorem of the verification
    must depend on NOTHING beyond Lean's three standard axioms
    (propext, Classical.choice, Quot.sound). A `sorry` inside any of
    these proofs surfaces here as sorryAx; `native_decide` in the
    corpus additionally refuses to evaluate sorry-tainted defs. This
    file prints one line per theorem; check.sh fails the gate unless
    every line is exactly the standard triple. -/
import Metalanguage.SubjectReduction

-- lattice covariance
#print axioms tmovesV_trans
#print axioms meetAtom_cov
#print axioms meetTy_cov
#print axioms removeTy_cov
#print axioms removeTy_nil_cov
#print axioms complNormals_cov
#print axioms complHasThrow_cov
-- expression-summary covariance (the 53-arm induction)
#print axioms typeOfE_cov
-- the one-step machine covariance
#print axioms step1_cov
-- the specialization layer (#8): decider stability + split covariance
#print axioms decMono_predDecide
#print axioms decMono_isCallable
#print axioms decMono_primDecide
#print axioms split1_cov
#print axioms splitP1_cov
-- the specLe relational layer (#8)
#print axioms specLe_flows_intro
#print axioms specLe_reject
#print axioms specLe_merge
#print axioms specLe_loop_join
#print axioms checkLoopBody_spec
#print axioms fold_specLe
-- the fork lift (#9)
#print axioms fork_specLe
-- the no-silent-falls invariant (56 arms)
#print axioms checkSeq_exits
-- the terminality-transfer layer (exit preservation)
#print axioms mergeTC_terminal
#print axioms fold_exits_true_of
#print axioms fold_terminal_falls_nil
#print axioms flatMap_falls_nil
#print axioms fork_lift
-- the kRet arm and its tools (the capstone's first full consumer)
#print axioms checkSeq_kRet_elim
#print axioms checkSeq_specialize_terminal
#print axioms frameOkUnder_elim
#print axioms SR_kRet
#print axioms SR_kMkList
#print axioms SR_kNewSlot
-- the SR arms proven so far
#print axioms SR_kIte
#print axioms SR_kPop
#print axioms SR_kSet
#print axioms SR_kEval_const
#print axioms SR_kEval_nat
#print axioms SR_kEval_nv
#print axioms SR_kEval_varNotPresent
#print axioms SR_kEval_isObject_nv
#print axioms SR_kEval_isNotObject_nv
#print axioms SR_kEval_isNotUndefined_nv
#print axioms SR_kEval_isU_nv
#print axioms SR_kEval_hasCall_nv
#print axioms SR_kEval_hasCtor_nv
#print axioms SR_kEval_isBoolVal_nv
#print axioms SR_kEval_isStrVal_nv
#print axioms SR_kEval_hasField_nv
#print axioms SR_kEval_isNullOrUnd_nv
#print axioms SR_kEval_isBoolVal_call_nv_fused
#print axioms SR_kTest
#print axioms SR_kTestVar_pIsObj
#print axioms SR_kTestVar_shape
#print axioms SR_kTestVar_pIsU
#print axioms SR_kTestVar_pIsNull
#print axioms SR_kTestVar_pNullOrUnd
#print axioms SR_kTestVar_pIsTrue
#print axioms SR_kTestVar_pIsFalse
#print axioms SR_kTestVar_pIsStr
#print axioms SR_kTestVar_pIsType
#print axioms SR_kTestVar_pIsCompletion
#print axioms SR_kTestVar_pIsNormalC
#print axioms SR_kTestVar_pIsThrowC
#print axioms SR_kTestVar_plainBool
#print axioms SR_kTestVar_pHasCall
#print axioms SR_kTestVar_pHasCtor
#print axioms SR_kTestVar_pHasField
#print axioms SR_kTestVar_pPred_unknown
#print axioms SR_kTestVar_pPred_split
#print axioms SR_kTestVar_pPred_data
#print axioms SR_kTestVar_pPred_acc
#print axioms SR_kUnwrap
#print axioms SR_kPrim1_pThrowC
#print axioms SR_kPrim1_pWrapC
#print axioms SR_kPrim1_bool
-- the kCall bridge (registry-hit arm)
#print axioms popArgs_le_take
#print axioms runtime_args_le
#print axioms callee_frameChecks
#print axioms fstep_kCall_found
#print axioms SR_kCall