import ETHIsFalse.Statement
import ETHIsFalse.Proof.Final

/-! The main theorems. The statements are in `Statement.lean`; the proofs are in `Proof/`. -/

/-- **The Exponential Time Hypothesis is false**: 3-SAT is decidable in time
`c · poly(n + m) · 2 ^ (n / r)` for every `r ≥ 1`. -/
theorem eth_is_false : ETHIsFalse.SubexponentialThreeSAT :=
  ETHIsFalse.Proof.subexponentialThreeSAT

/-- Counting the satisfying assignments of `w`-CNF formulas, for every `w`, within the same time. -/
theorem sharpSAT_subexponential : ETHIsFalse.SubexponentialSharpSAT :=
  ETHIsFalse.Proof.subexponentialSharpSAT

#print axioms eth_is_false
#print axioms sharpSAT_subexponential
