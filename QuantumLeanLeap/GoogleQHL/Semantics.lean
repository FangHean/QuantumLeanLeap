import QuantumLeanLeap.GoogleQHL.WP
import Mathlib.Data.List.FinRange

/-! Forward, finite-unrolling semantics. A list retains separate measurement
histories, including histories with the same classical store. Matrices are
unnormalized: their traces carry branch probabilities. Zero fuel aborts only
loops, never primitive commands. Nested loops use the preceding fuel in a body,
exactly as in `wpApprox`. No density matrix is normalized after measurement. -/
namespace QuantumLeanLeap.GoogleQHL

variable {Var : Type} {d : Nat}

abbrev Branch (Var : Type) (d : Nat) := Store Var × Operator d

def conjugate (K rho : Operator d) : Operator d :=
  K * rho * Matrix.conjTranspose K

def resetState (index : Fin d) (rho : Operator d) : Operator d :=
  Matrix.single index index rho.trace

def interpApprox [DecidableEq Var] : QProg Var d → Nat → Branch Var d → List (Branch Var d)
  | .skip, _, input => [input]
  | .abort, _, _ => []
  | .assign target expression, _, (store, rho) =>
      [(Function.update store target (expression store), rho)]
  | .qset index, _, (store, rho) => [(store, resetState index rho)]
  | .apply U, _, (store, rho) => [(store, conjugate U.matrix rho)]
  | .measure target count M, _, (store, rho) =>
      (List.finRange count).map fun o =>
        (Function.update store target (o.val : Int), conjugate (M.kraus o) rho)
  | .seq first second, fuel, input =>
      (interpApprox first fuel input).flatMap (interpApprox second fuel)
  | .qif guard first second, fuel, input =>
      if guard input.1 then interpApprox first fuel input else interpApprox second fuel input
  | .qwhile guard body, fuel, input =>
      Nat.rec (motive := fun _ => Branch Var d → List (Branch Var d))
        (fun _ => [])
        (fun k previous current => if guard current.1 then
          (interpApprox body k current).flatMap previous else [current]) fuel input

/-- Algebraic trace pairing; positivity is proved separately for physical inputs. -/
def pairing (effect rho : Operator d) : Real := (effect * rho).trace.re

def branchExpectation (post : CQPredicate Var d) : List (Branch Var d) → Real
  | [] => 0
  | b :: rest => pairing (post b.1) b.2 + branchExpectation post rest

@[simp] theorem branchExpectation_nil (post : CQPredicate Var d) :
    branchExpectation post [] = 0 := rfl

@[simp] theorem branchExpectation_cons (post : CQPredicate Var d)
    (b : Branch Var d) (rest : List (Branch Var d)) :
    branchExpectation post (b :: rest) =
      pairing (post b.1) b.2 + branchExpectation post rest := rfl

theorem branchExpectation_append (post : CQPredicate Var d)
    (a b : List (Branch Var d)) :
    branchExpectation post (a ++ b) = branchExpectation post a + branchExpectation post b := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc]

theorem branchExpectation_flatMap (post : CQPredicate Var d) (inputs : List (Branch Var d))
    (next : Branch Var d → List (Branch Var d)) :
    branchExpectation post (inputs.flatMap next) =
      (inputs.map fun b => branchExpectation post (next b)).sum := by
  induction inputs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, branchExpectation_append, ih]

theorem branchExpectation_map {α : Type} (post : CQPredicate Var d)
    (inputs : List α) (f : α → Branch Var d) :
    branchExpectation post (inputs.map f) =
      (inputs.map fun a => pairing (post (f a).1) (f a).2).sum := by
  induction inputs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem branchExpectation_eq_sum (post : CQPredicate Var d) (inputs : List (Branch Var d)) :
    branchExpectation post inputs = (inputs.map fun b => pairing (post b.1) b.2).sum := by
  simpa using branchExpectation_map post inputs id

@[simp] theorem interpApprox_while_zero [DecidableEq Var] (g : Store Var → Bool)
    (body : QProg Var d) (input : Branch Var d) :
    interpApprox (.qwhile g body) 0 input = [] := rfl

@[simp] theorem interpApprox_while_succ [DecidableEq Var] (g : Store Var → Bool)
    (body : QProg Var d) (fuel : Nat) (input : Branch Var d) :
    interpApprox (.qwhile g body) (fuel + 1) input =
      if g input.1 then (interpApprox body fuel input).flatMap
        (interpApprox (.qwhile g body) fuel) else [input] := rfl

end QuantumLeanLeap.GoogleQHL
