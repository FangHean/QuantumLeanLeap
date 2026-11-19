import QuantumLeanLeap.GoogleQHL.Verification.ResetSpec
import QuantumLeanLeap.GoogleQHL.Circuits.Gates

namespace QuantumLeanLeap.GoogleQHL.Verification.ResetLanguage
open Matrix

/-- A closed, loop-free one-qubit submission language. No reset instruction,
oracle, arbitrary matrix, cost annotation, or proof is supplied by candidates. -/
inductive Program where
  | skip | x | z | measure
  | seq (a b : Program)
  | ifZero (zero nonzero : Program)
  deriving Repr

def xUnitary : Unitary 2 where
  matrix := !![0, 1; 1, 0]
  left_inverse := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  right_inverse := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

def zUnitary : Unitary 2 where
  matrix := !![1, 0; 0, -1]
  left_inverse := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  right_inverse := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

def Program.compile : Program → QProg Unit 2
  | .skip => .skip
  | .x => .apply xUnitary
  | .z => .apply zUnitary
  | .measure => .measure () 2 (Circuits.wireMeasurement (n := 1) 0)
  | .seq a b => .seq a.compile b.compile
  | .ifZero a b => .qif (fun s => decide (s () = 0)) a.compile b.compile

theorem Program.fuel_independent (p : Program) (k j : Nat) (input : Branch Unit 2) :
    interpApprox p.compile k input = interpApprox p.compile j input := by
  induction p generalizing input with
  | skip => rfl
  | x => rfl
  | z => rfl
  | measure => rfl
  | seq a b iha ihb =>
      simp only [compile, interpApprox, iha]
      congr 1
      funext b
      exact ihb b
  | ifZero a b iha ihb => simp only [compile, interpApprox, iha, ihb]

end QuantumLeanLeap.GoogleQHL.Verification.ResetLanguage
