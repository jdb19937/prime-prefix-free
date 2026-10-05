/- Verification harness. Each `#guard_msgs` block fails elaboration unless
`#print axioms` reports exactly Lean's three standard axioms. -/
import PPF

/-- info: 'ppf_hasSum_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ppf_hasSum_of_RH

/-- info: 'PPF.summable_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PPF.summable_of_inputs

/-- info: 'PPF.pairSieve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PPF.pairSieve

/-- info: 'PPF.selbergMeanSquare_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PPF.selbergMeanSquare_of_RH

/-- info: 'PPF.Explicit.tsum_le_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PPF.Explicit.tsum_le_of_RH
