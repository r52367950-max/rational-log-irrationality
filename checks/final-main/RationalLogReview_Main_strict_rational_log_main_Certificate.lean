import Round2MainReference
import Round2MainTypeChecker
import RationalLogMain

set_option autoImplicit false

namespace RationalLogReview.IndependentFinalCheck
theorem statement_certificate :
    RationalLogReview.MainReference.StrictRationalLogMain :=
  RationalLogReview.Main.strict_rational_log_main
end RationalLogReview.IndependentFinalCheck

#print axioms RationalLogReview.IndependentFinalCheck.statement_certificate
