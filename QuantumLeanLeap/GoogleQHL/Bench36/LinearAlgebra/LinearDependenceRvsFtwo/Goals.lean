import QuantumLeanLeap.GoogleQHL.Bench36.LinearAlgebra.LinearDependenceRvsFtwo.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.LinearDependenceRvsFtwo
set_option linter.unusedVariables false
noncomputable section


def obligation_0  : Prop :=
  LinearIndependent ℝ vectorFamilyR ∧

    ¬LinearIndependent (ZMod 2) vectorFamilyF ∧

    (Submodule.span (ZMod 2) (Set.range vectorFamilyF) : Set (Fin 3 → ZMod 2)) =
      {w | w = 0 ∨ w = v1F ∨ w = v2F ∨ w = v3F}

end
end QuantumLeanLeap.GoogleQHL.Bench36.LinearDependenceRvsFtwo
