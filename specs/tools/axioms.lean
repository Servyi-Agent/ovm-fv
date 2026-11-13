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
-- the Γ-split covariance
#print axioms split1_cov
-- the one-step machine covariance
#print axioms step1_cov
-- the no-silent-falls invariant (56 arms)
#print axioms checkSeq_exits
-- the SR arms proven so far
#print axioms SR_kIte
#print axioms SR_kPop
#print axioms SR_kSet
#print axioms SR_kEval_const

