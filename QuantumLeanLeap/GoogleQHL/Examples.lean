import QuantumLeanLeap.GoogleQHL.WP
import QuantumLeanLeap.GoogleQHL.ResourceCounting

/-! Small executable/theorem checks for the reconstructed interface. -/

namespace QuantumLeanLeap.GoogleQHL.Examples

open QuantumLeanLeap.GoogleQHL

inductive Var where
  | counter
  | outcome
deriving DecidableEq

def increment : QProg Var 2 :=
  .assign .counter fun store => store .counter + 1

def zeroCostModel : CostModel 2 where
  assignmentCost := 0
  resetCost := 0
  unitaryCost := fun _ => 0
  measurementCost := fun _ => 0

theorem increment_wp (fuel : Nat) (post : CQPredicate Var 2) (store : Store Var) :
    wpApprox increment fuel post store =
      post (Function.update store .counter (store .counter + 1)) := rfl

theorem increment_zero_cost (fuel : Nat) :
    worstCost zeroCostModel increment fuel = 0 := rfl

end QuantumLeanLeap.GoogleQHL.Examples
