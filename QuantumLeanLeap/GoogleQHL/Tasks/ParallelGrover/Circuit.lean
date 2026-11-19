import QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover.ExactFour

/-! A restricted straight-line query language. Free matrices are fixed before
the marked predicate is supplied to interpretation. One oracle node denotes
one parallel round, not m rounds. Adaptive programs are a future extension. -/
namespace QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover
open scoped BigOperators
open Matrix
noncomputable section
variable {N m : Nat}

structure FreeGate (N m : Nat) where
  matrix : Matrix (Address N m) (Address N m) Complex
  unitary : matrix.conjTranspose * matrix = 1

inductive Circuit (N m : Nat) where
  | free (gate : FreeGate N m)
  | query
  | seq (first second : Circuit N m)

def Circuit.rounds : Circuit N m → Nat
  | .free _ => 0
  | .query => 1
  | .seq a b => a.rounds + b.rounds

def phaseMatrix (marked : Fin N → Bool) : Matrix (Address N m) (Address N m) Complex :=
  Matrix.diagonal (fun x => ∏ j, sign (marked (x j)))

theorem phaseMatrix_mulVec (marked : Fin N → Bool) (v : Address N m → Complex) :
    phaseMatrix marked *ᵥ v = phaseAction marked v := by
  funext x
  simp [phaseMatrix, Matrix.mulVec, dotProduct, Matrix.diagonal, phaseAction]

theorem phaseMatrix_unitary (marked : Fin N → Bool) :
    (phaseMatrix (m := m) marked).conjTranspose * phaseMatrix marked = 1 := by
  have hs (b : Bool) : star (sign b) * sign b = 1 := by cases b <;> norm_num [sign]
  simp only [phaseMatrix, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have h : (fun x : Address N m => star (∏ j, sign (marked (x j))) *
      (∏ j, sign (marked (x j)))) = fun _ => (1 : Complex) := by
    funext x
    simp only [star_prod, ← Finset.prod_mul_distrib, hs, Finset.prod_const_one]
  change Matrix.diagonal (fun x : Address N m => star (∏ j, sign (marked (x j))) *
    (∏ j, sign (marked (x j)))) = 1
  rw [h]
  exact Matrix.diagonal_one

def Circuit.matrix (marked : Fin N → Bool) : Circuit N m → Matrix (Address N m) (Address N m) Complex
  | .free U => U.matrix
  | .query => phaseMatrix marked
  | .seq a b => b.matrix marked * a.matrix marked

theorem Circuit.unitary (c : Circuit N m) (marked : Fin N → Bool) :
    (c.matrix marked).conjTranspose * c.matrix marked = 1 := by
  induction c with
  | free U => exact U.unitary
  | query => exact phaseMatrix_unitary marked
  | seq a b ha hb =>
    simp only [Circuit.matrix, Matrix.conjTranspose_mul]
    calc
      _ = (a.matrix marked).conjTranspose *
          ((b.matrix marked).conjTranspose * b.matrix marked) * a.matrix marked := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hb, Matrix.mul_one, ha]

/-- This syntax is independent of `target` and works for every singleton oracle. -/
def exactFourCircuit (m : Nat) : Circuit 4 m :=
  .seq (.free ⟨tensorPower m prepareFour, tensorPower_unitary _ prepareFour_unitary⟩)
    (.seq .query (.free ⟨tensorPower m diffusionFour, tensorPower_unitary _ diffusionFour_unitary⟩))

theorem exactFourCircuit_rounds (m : Nat) : (exactFourCircuit m).rounds = 1 := rfl

/-- From zero address registers, the actual interpreted circuit outputs the mark in every slot. -/
theorem exactFourCircuit_output (m : Nat) (target : Fin 4) :
    (exactFourCircuit m).matrix (singletonMark target) *ᵥ
      (fun x => if x = (fun _ => 0) then 1 else 0) =
      (fun x => if x = (fun _ => target) then 1 else 0) := by
  rw [← productState_delta (m := m) (0 : Fin 4)]
  simp only [exactFourCircuit, Circuit.matrix, ← Matrix.mulVec_mulVec,
    tensorPower_mulVec, prepareFour_zero, phaseMatrix_mulVec]
  exact exactFourOutput_eq m target

/-- The query node is implemented by the paper's reversible bit oracle,
including on entangled address amplitudes rather than only product inputs. -/
theorem query_bit_oracle_bridge (marked : Fin N → Bool) (v : Address N m → Complex) :
    oracle marked *ᵥ minusLift v = minusLift ((Circuit.query : Circuit N m).matrix marked *ᵥ v) := by
  rw [Circuit.matrix, phaseMatrix_mulVec]
  exact oracle_phase_kickback marked v

end
end QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover
