import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/




namespace QuantumLeanLeap.GoogleQHL.Bench36.BitOracleUnitaryHermitian

noncomputable section
variable {n m : ℕ}

abbrev BitReg (n m : ℕ) := (Fin n → Bool) × (Fin m → Bool)

def boolFunXor (a b : Fin m → Bool) : Fin m → Bool :=
  fun i => (a i).xor (b i)

def bitOraclePerm (f : (Fin n → Bool) → (Fin m → Bool)) :
    Equiv.Perm ((Fin n → Bool) × (Fin m → Bool)) where
  toFun p := (p.1, boolFunXor p.2 (f p.1))
  invFun p := (p.1, boolFunXor p.2 (f p.1))
  left_inv p := by
    rcases p with ⟨p1, p2⟩
    change (p1, boolFunXor (boolFunXor p2 (f p1)) (f p1)) = (p1, p2)
    apply Prod.ext
    · rfl
    · funext i
      simp only [boolFunXor]
      cases p2 i <;> cases f p1 i <;> rfl
  right_inv p := by
    rcases p with ⟨p1, p2⟩
    change (p1, boolFunXor (boolFunXor p2 (f p1)) (f p1)) = (p1, p2)
    apply Prod.ext
    · rfl
    · funext i
      simp only [boolFunXor]
      cases p2 i <;> cases f p1 i <;> rfl

def bitOracle (f : (Fin n → Bool) → (Fin m → Bool)) : Mat (BitReg n m) :=
  permMatrix (bitOraclePerm f)

end

end QuantumLeanLeap.GoogleQHL.Bench36.BitOracleUnitaryHermitian
