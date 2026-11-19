import QuantumLeanLeap.GoogleQHL.Semantics
import QuantumLeanLeap.GoogleQHL.ResourceCounting

/-! Independent specification for a small LOCAL acceptance benchmark.
It imports neither the candidate language nor a candidate implementation.
This is not one of the five Google paper benchmarks. -/
namespace QuantumLeanLeap.GoogleQHL.Verification.ResetSpec

def gateCost : CostModel 2 := ⟨0, 0, fun _ => 1, fun _ => 0⟩
def measurementCost : CostModel 2 := ⟨0, 0, fun _ => 0, fun _ => 1⟩

/-- Discarding the classical result must leave exactly tr(rho)|0><0|.
All complex matrices are quantified, so coherent and mixed inputs are covered.
The classical output is deliberately unspecified. Budgets count worst paths. -/
def Contract (p : QProg Unit 2) : Prop :=
  (∀ fuel (s : Store Unit) (rho : Operator 2),
    ((interpApprox p fuel (s, rho)).map Prod.snd).sum = resetState 0 rho) ∧
  (∀ fuel, worstCost gateCost p fuel ≤ 1) ∧
  (∀ fuel, worstCost measurementCost p fuel ≤ 1)

end QuantumLeanLeap.GoogleQHL.Verification.ResetSpec
