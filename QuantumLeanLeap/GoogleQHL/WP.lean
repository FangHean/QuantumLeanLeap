import QuantumLeanLeap.GoogleQHL.Syntax

/-!
# Bounded weakest preconditions

This file reconstructs the weakest-precondition equations published in the
paper. `wpApprox program fuel post` gives the finite-unrolling approximation:
zero loop unfoldings behave like `abort`, while `fuel + 1` unfoldings execute
one body and continue with the preceding approximation.

The algebraic result is an unbundled `CQPredicate`. `Order.lean` proves effect
preservation and bundles `wpBounded`; `Unbounded.lean` constructs `wp` as an
operator least upper bound with forward-expectation duality.
-/

namespace QuantumLeanLeap.GoogleQHL

open scoped ComplexOrder MatrixOrder

variable {Var : Type} {d : Nat}

/-- Weakest-precondition approximation obtained by finitely unrolling loops. -/
def wpApprox [DecidableEq Var] : QProg Var d → Nat → CQPredicate Var d → CQPredicate Var d
  | .skip, _, post => post
  | .abort, _, _ => 0
  | .assign target expression, _, post =>
      fun store => post (Function.update store target (expression store))
  | .qset zeroIndex, _, post =>
      fun store => Matrix.scalar (Fin d) (post store zeroIndex zeroIndex)
  | .apply unitary, _, post =>
      fun store => Matrix.conjTranspose unitary.matrix * post store * unitary.matrix
  | .measure target _ measurement, _, post =>
      fun store => ∑ outcome,
        Matrix.conjTranspose (measurement.kraus outcome) *
          post (Function.update store target (outcome.val : Int)) *
          measurement.kraus outcome
  | .seq first second, fuel, post =>
      wpApprox first fuel (wpApprox second fuel post)
  | .qif guard thenBranch elseBranch, fuel, post =>
      fun store =>
        if guard store then wpApprox thenBranch fuel post store
        else wpApprox elseBranch fuel post store
  | .qwhile guard body, fuel, post =>
      Nat.rec (motive := fun _ => CQPredicate Var d)
        0
        (fun previousFuel previous => fun store =>
          if guard store then wpApprox body previousFuel previous store else post store)
        fuel

@[simp] theorem wpApprox_skip [DecidableEq Var] (fuel : Nat) (post : CQPredicate Var d) :
    wpApprox (.skip : QProg Var d) fuel post = post := rfl

@[simp] theorem wpApprox_abort [DecidableEq Var] (fuel : Nat) (post : CQPredicate Var d) :
    wpApprox (.abort : QProg Var d) fuel post = 0 := rfl

@[simp] theorem wpApprox_seq [DecidableEq Var]
    (first second : QProg Var d) (fuel : Nat) (post : CQPredicate Var d) :
    wpApprox (.seq first second) fuel post =
      wpApprox first fuel (wpApprox second fuel post) := rfl

@[simp] theorem wpApprox_while_zero [DecidableEq Var]
    (guard : Store Var → Bool) (body : QProg Var d) (post : CQPredicate Var d) :
    wpApprox (.qwhile guard body) 0 post = 0 := rfl

@[simp] theorem wpApprox_while_succ [DecidableEq Var]
    (guard : Store Var → Bool) (body : QProg Var d) (fuel : Nat)
    (post : CQPredicate Var d) :
    wpApprox (.qwhile guard body) (fuel + 1) post =
      fun store => if guard store then
        wpApprox body fuel (wpApprox (.qwhile guard body) fuel post) store
      else post store := by
  funext store
  simp only [wpApprox]

/-- Sequential unitary application has the expected Heisenberg-picture order. -/
theorem wpApprox_two_unitaries [DecidableEq Var]
    (first second : Unitary d) (fuel : Nat) (post : CQPredicate Var d)
    (store : Store Var) :
    wpApprox (.seq (.apply first) (.apply second)) fuel post store =
      Matrix.conjTranspose first.matrix *
        (Matrix.conjTranspose second.matrix * post store * second.matrix) * first.matrix := rfl

end QuantumLeanLeap.GoogleQHL
