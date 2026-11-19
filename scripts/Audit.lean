import QuantumLeanLeap

open QuantumLeanLeap.GoogleVQCC.InvSqrt

-- These must show only standard Lean/mathlib axioms, never sorryAx.
#print axioms quantizedTurns_accurate
#print axioms wrappedTurns_accurate
#print axioms compile_trace_length
#print axioms SemanticCertificate.apply_superposition
#print axioms newton_defect_identity
#print axioms newtonWordStep_interval
#print axioms newtonTurns_accurate

#eval phaseWord 1
#eval phaseWord 4
#eval wrappedPhaseWord 1
#eval phaseWord 3133452
#eval newtonWord 1 6
#eval newtonWord 4 6
#eval newtonWord 3133452 6
