import QuantumLeanLeap.GoogleQHL.Syntax

/-!
# Syntactic worst-case resource accounting

This is the first, state-independent layer of the paper's cost framework. It
computes exact costs for straight-line programs, takes the larger conditional
branch, and uses the same finite loop bound as `wpApprox`.
-/

namespace QuantumLeanLeap.GoogleQHL

variable {Var : Type} {d : Nat}

/-- User-selected primitive costs. This can represent T count, oracle queries,
or another additive logical resource. -/
structure CostModel (d : Nat) where
  assignmentCost : Nat
  resetCost : Nat
  unitaryCost : Unitary d → Nat
  measurementCost : {outcomes : Nat} → Measurement d outcomes → Nat

/-- Worst-case cost with at most `fuel` iterations of each loop. -/
def worstCost (model : CostModel d) : QProg Var d → Nat → Nat
  | .skip, _ => 0
  | .abort, _ => 0
  | .assign .., _ => model.assignmentCost
  | .qset .., _ => model.resetCost
  | .apply unitary, _ => model.unitaryCost unitary
  | .measure _ _ measurement, _ => model.measurementCost measurement
  | .seq first second, fuel => worstCost model first fuel + worstCost model second fuel
  | .qif _ thenBranch elseBranch, fuel =>
      max (worstCost model thenBranch fuel) (worstCost model elseBranch fuel)
  | .qwhile _ body, fuel => fuel * worstCost model body fuel

@[simp] theorem worstCost_seq (model : CostModel d) (first second : QProg Var d) (fuel : Nat) :
    worstCost model (.seq first second) fuel =
      worstCost model first fuel + worstCost model second fuel := rfl

@[simp] theorem worstCost_while (model : CostModel d) (guard : Store Var → Bool)
    (body : QProg Var d) (fuel : Nat) :
    worstCost model (.qwhile guard body) fuel = fuel * worstCost model body fuel := rfl

end QuantumLeanLeap.GoogleQHL
