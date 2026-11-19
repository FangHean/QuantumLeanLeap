import QuantumAlg

/-!
# Canonical correctness certificates

Each definition below is a direct proof-valued alias of a theorem in
`Lean-QuantumAlg`.  Importing this module therefore checks that the complete
public endpoints remain present and type-correct under the pinned dependency.
-/

namespace QuantumLeanLeap.Algorithms.Certificates

alias bernsteinVazirani := QuantumAlg.BernsteinVazirani.main
alias deutschJozsa := QuantumAlg.DeutschJozsa.main
alias simon := QuantumAlg.SimonsProblem.main
alias groverSearch := QuantumAlg.GroverSearch.main
alias quantumPhaseEstimation := QuantumAlg.QuantumPhaseEstimation.main
alias amplitudeEstimation := QuantumAlg.AmplitudeEstimation.main
alias teleportation := QuantumAlg.QuantumTeleportation.main
alias superdenseCoding := QuantumAlg.SuperdenseCoding.main
alias exactOrderFinding := QuantumAlg.OrderFinding.Exact.NativeEndpoint.main
alias integerFactoring := QuantumAlg.Factoring.ShorStyle.main
alias finiteCyclicDLP := QuantumAlg.FiniteCyclicDLP.main
alias ellipticCurveDLP := QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.main

end QuantumLeanLeap.Algorithms.Certificates
