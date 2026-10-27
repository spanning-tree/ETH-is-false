import ETHIsFalse.Proof.Reduction
import OAI.Algorithms.SubexponentialSAT.Main

/-! The statements, from OpenAI's proof of `SqrtLogSpace.exact_count_and_sat`. -/

namespace ETHIsFalse.Proof

open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem subexponentialThreeSAT_cslib : SubexponentialThreeSATCslib :=
  ethIsFalse_of (exact_count_and_sat 3 (by norm_num))

theorem subexponentialSharpSAT_cslib : SubexponentialSharpSATCslib :=
  countingIsSubexponential_of exact_count_and_sat

theorem subexponentialThreeSAT : SubexponentialThreeSAT :=
  subexponentialThreeSAT_of_cslib subexponentialThreeSAT_cslib

theorem subexponentialSharpSAT : SubexponentialSharpSAT :=
  subexponentialSharpSAT_of_cslib subexponentialSharpSAT_cslib

end ETHIsFalse.Proof
