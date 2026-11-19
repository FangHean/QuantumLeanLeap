import QuantumLeanLeap.GoogleQHL.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Appendix E's bit oracle and simultaneous queries on disjoint registers.
`N` is the address-space size; the paper instantiates it as `2^n`. -/
namespace QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover
open scoped BigOperators
open Matrix
variable {N m : Nat}

abbrev Slot (N : Nat) := Bool × Fin N
abbrev QueryBasis (N m : Nat) := Fin m → Slot N
abbrev Address (N m : Nat) := Fin m → Fin N

def flip (marked : Fin N → Bool) (a : Slot N) : Slot N :=
  (xor a.1 (marked a.2), a.2)

theorem flip_involutive (marked : Fin N → Bool) : Function.Involutive (flip marked) := by
  rintro ⟨b, x⟩
  cases b <;> cases h : marked x <;> simp [flip, h]

def oraclePerm (marked : Fin N → Bool) : Equiv.Perm (QueryBasis N m) where
  toFun a j := flip marked (a j)
  invFun a j := flip marked (a j)
  left_inv a := funext fun j => flip_involutive marked (a j)
  right_inv a := funext fun j => flip_involutive marked (a j)

noncomputable def oracle (marked : Fin N → Bool) :
    Matrix (QueryBasis N m) (QueryBasis N m) Complex := (oraclePerm marked).permMatrix Complex

theorem oracle_unitary (marked : Fin N → Bool) :
    (oracle (m := m) marked).conjTranspose * oracle marked = 1 ∧
      oracle (m := m) marked * (oracle marked).conjTranspose = 1 := by
  constructor <;> simp only [oracle, Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  · simp
  · simp

def sign (b : Bool) : Complex := if b then -1 else 1

theorem sign_xor (a b : Bool) : sign (xor a b) = sign a * sign b := by
  cases a <;> cases b <;> norm_num [sign]

/-- Tensor with unnormalised `|->` targets. A common normalisation scalar
may be restored by linearity; no probability is assigned to this lift. -/
noncomputable def minusLift (v : Address N m → Complex) (a : QueryBasis N m) : Complex :=
  (∏ j, sign (a j).1) * v (fun j => (a j).2)

noncomputable def phaseAction (marked : Fin N → Bool) (v : Address N m → Complex)
    (x : Address N m) : Complex := (∏ j, sign (marked (x j))) * v x

/-- All m phase queries are induced by one simultaneous bit-oracle call. -/
theorem oracle_phase_kickback (marked : Fin N → Bool) (v : Address N m → Complex) :
    oracle marked *ᵥ minusLift v = minusLift (phaseAction marked v) := by
  rw [oracle, Matrix.permMatrix_mulVec]
  funext a
  change (∏ j, sign (xor (a j).1 (marked (a j).2))) * v (fun j => (a j).2) =
    (∏ j, sign (a j).1) * ((∏ j, sign (marked (a j).2)) * v (fun j => (a j).2))
  simp only [sign_xor, Finset.prod_mul_distrib]
  ring

/-- An all-`|+>` target register is transparent to the bit oracle. -/
theorem oracle_plus_targets (marked : Fin N → Bool) (v : Address N m → Complex) :
    oracle (m := m) marked *ᵥ (fun a => v (fun j => (a j).2)) =
      (fun a => v (fun j => (a j).2)) := by
  rw [oracle, Matrix.permMatrix_mulVec]
  rfl

end QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover
