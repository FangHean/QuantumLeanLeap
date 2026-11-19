import QuantumLeanLeap.GoogleQHL.Bench36.Fourier.FiniteQFTUnitarity.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.FiniteQFTUnitarity
set_option linter.unusedVariables false
noncomputable section
variable (M : ℕ+)

def obligation_0  : Prop :=
  qftMatrix M ∈ Matrix.unitaryGroup (Fin M) ℂ

end
end QuantumLeanLeap.GoogleQHL.Bench36.FiniteQFTUnitarity
