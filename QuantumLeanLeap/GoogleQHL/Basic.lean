import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# A clean-room core for Google's classical--quantum Hoare logic

This namespace reconstructs the public mathematical interface described in
Appendix A of *Discovering formally verified quantum programs with AI*.
It is a clean-room implementation, not a mirror of Google's source library.
-/

namespace QuantumLeanLeap.GoogleQHL

open scoped ComplexOrder MatrixOrder

variable {Var : Type} {d : Nat}

/-- Classical stores use integer-valued variables, as in the paper. -/
abbrev Store (Var : Type) : Type := Var → Int

/-- A finite-dimensional quantum operator. -/
abbrev Operator (d : Nat) : Type := Matrix (Fin d) (Fin d) Complex

/-- Partial density operators: positive semidefinite matrices of trace at most one.

The real part is used in the trace bound so the definition is well typed before
deriving that the trace of a positive semidefinite matrix is real. -/
structure PartialDensity (d : Nat) where
  matrix : Operator d
  positive : matrix.PosSemidef
  trace_le_one : matrix.trace.re ≤ 1

/-- A classical--quantum substate. Missing total trace represents
nontermination, exactly as in the public paper description. -/
structure CQState (Var : Type) (d : Nat) where
  density : Store Var → PartialDensity d
  mass : Real
  trace_hasSum : HasSum (fun store => (density store).matrix.trace.re) mass
  mass_le_one : mass ≤ 1

/-- Unit-interval observables, the quantum predicates of the Hoare logic. -/
structure Observable (d : Nat) where
  matrix : Operator d
  nonnegative : (0 : Operator d) ≤ matrix
  le_identity : matrix ≤ 1

/-- A classical--quantum assertion maps each classical store to an observable. -/
abbrev CQAssertion (Var : Type) (d : Nat) : Type := Store Var → Observable d

/-- The unbundled predicate type used while reconstructing preservation proofs. -/
abbrev CQPredicate (Var : Type) (d : Nat) : Type := Store Var → Operator d

/-- A certified unitary matrix. Both equations are retained because they are
convenient in program proofs and avoid depending on an invertibility conversion. -/
structure Unitary (d : Nat) where
  matrix : Operator d
  left_inverse : Matrix.conjTranspose matrix * matrix = 1
  right_inverse : matrix * Matrix.conjTranspose matrix = 1

/-- A finite-outcome, possibly sub-unital measurement.

`complete` is an inequality rather than equality so the same object can model
the partial states used for nontermination in the paper. -/
structure Measurement (d outcomes : Nat) where
  kraus : Fin outcomes → Operator d
  complete : (∑ o, Matrix.conjTranspose (kraus o) * kraus o) ≤ 1

/-- The identity operator, bundled as a unitary. -/
def Unitary.identity (d : Nat) : Unitary d where
  matrix := 1
  left_inverse := by
    rw [Matrix.conjTranspose_one, one_mul]
  right_inverse := by
    rw [Matrix.conjTranspose_one, mul_one]

/-- Heisenberg pullback of an observable through a unitary. -/
def Observable.pullback (predicate : Observable d) (unitary : Unitary d) : Observable d where
  matrix := Matrix.conjTranspose unitary.matrix * predicate.matrix * unitary.matrix
  nonnegative := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact (Matrix.nonneg_iff_posSemidef.mp predicate.nonnegative).conjTranspose_mul_mul_same
      unitary.matrix
  le_identity := by
    rw [Matrix.le_iff]
    have h := (Matrix.le_iff.mp predicate.le_identity).conjTranspose_mul_mul_same unitary.matrix
    convert h using 1
    calc
      1 - Matrix.conjTranspose unitary.matrix * predicate.matrix * unitary.matrix =
          Matrix.conjTranspose unitary.matrix * unitary.matrix -
            Matrix.conjTranspose unitary.matrix * predicate.matrix * unitary.matrix := by
              rw [unitary.left_inverse]
      _ = Matrix.conjTranspose unitary.matrix * (1 - predicate.matrix) * unitary.matrix := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]

/-- Expectation of an assertion in a classical--quantum substate.

The convergence and unit-interval proofs are in `Expectation.lean`. -/
noncomputable def expectation (state : CQState Var d) (assertion : CQAssertion Var d) : Real :=
  ∑' store, ((assertion store).matrix * (state.density store).matrix).trace.re

/-- Forget the proof fields of an assertion. -/
def CQAssertion.toPredicate (assertion : CQAssertion Var d) : CQPredicate Var d :=
  fun store => (assertion store).matrix

end QuantumLeanLeap.GoogleQHL
