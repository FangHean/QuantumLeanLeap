import QuantumLeanLeap.GoogleQHL.Bench36.Circuits.ControlledPhaseFromCNOTHadamards.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.ControlledPhaseFromCNOTHadamards
set_option linter.unusedVariables false
noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36

def obligation_0  : Prop :=
  controlled Z =
      tensorOp (1 : Operator (2 ^ 1)) H * CNOT *
        tensorOp (1 : Operator (2 ^ 1)) H

end
end QuantumLeanLeap.GoogleQHL.Bench36.ControlledPhaseFromCNOTHadamards
