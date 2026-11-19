import QuantumLeanLeap.GoogleQHL.Bench36.Circuits.ControlledRYTwoCNOTSynthesis.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.ControlledRYTwoCNOTSynthesis
set_option linter.unusedVariables false
noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36

def obligation_0 (θ : ℝ) : Prop :=
  controlled (rotY θ) =
      tensorOp (1 : Operator (2 ^ 1)) (rotY (θ / 2)) * CNOT *
        tensorOp (1 : Operator (2 ^ 1)) (rotY (-(θ / 2))) * CNOT

end
end QuantumLeanLeap.GoogleQHL.Bench36.ControlledRYTwoCNOTSynthesis
