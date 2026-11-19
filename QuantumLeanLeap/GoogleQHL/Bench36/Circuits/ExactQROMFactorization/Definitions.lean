import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/




namespace QuantumLeanLeap.GoogleQHL.Bench36.ExactQROMFactorization

noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36
variable {n m : ℕ}

abbrev QReg (n m : ℕ) := (Fin n → Bool) × (Fin m → Bool)

def boolFunXor (a b : Fin m → Bool) : Fin m → Bool :=
  fun i => (a i).xor (b i)

def qromPerm (D : (Fin n → Bool) → (Fin m → Bool)) :
    Equiv.Perm ((Fin n → Bool) × (Fin m → Bool)) where
  toFun p := (p.1, boolFunXor p.2 (D p.1))
  invFun p := (p.1, boolFunXor p.2 (D p.1))
  left_inv p := by
    rcases p with ⟨p1, p2⟩
    change (p1, boolFunXor (boolFunXor p2 (D p1)) (D p1)) = (p1, p2)
    apply Prod.ext
    · rfl
    · funext i
      simp only [boolFunXor]
      cases p2 i <;> cases D p1 i <;> rfl
  right_inv p := by
    rcases p with ⟨p1, p2⟩
    change (p1, boolFunXor (boolFunXor p2 (D p1)) (D p1)) = (p1, p2)
    apply Prod.ext
    · rfl
    · funext i
      simp only [boolFunXor]
      cases p2 i <;> cases D p1 i <;> rfl

def qromOracle (D : (Fin n → Bool) → (Fin m → Bool)) : Mat (QReg n m) :=
  permMatrix (qromPerm D)

def addressPerm (D : (Fin n → Bool) → (Fin m → Bool)) (k : Fin n → Bool) :
    Equiv.Perm ((Fin n → Bool) × (Fin m → Bool)) where
  toFun p := if p.1 = k then (p.1, boolFunXor p.2 (D k)) else p
  invFun p := if p.1 = k then (p.1, boolFunXor p.2 (D k)) else p
  left_inv p := by
    obtain ⟨p1, p2⟩ := p
    by_cases h : p1 = k
    · have hcancel : boolFunXor (boolFunXor p2 (D k)) (D k) = p2 := by
        funext i
        simp only [boolFunXor]
        cases p2 i <;> cases D k i <;> rfl
      simp [h, hcancel]
    · simp [h]
  right_inv p := by
    obtain ⟨p1, p2⟩ := p
    by_cases h : p1 = k
    · have hcancel : boolFunXor (boolFunXor p2 (D k)) (D k) = p2 := by
        funext i
        simp only [boolFunXor]
        cases p2 i <;> cases D k i <;> rfl
      simp [h, hcancel]
    · simp [h]

def Ck (D : (Fin n → Bool) → (Fin m → Bool)) (k : Fin n → Bool) : Mat (QReg n m) :=
  permMatrix (addressPerm D k)

end

end QuantumLeanLeap.GoogleQHL.Bench36.ExactQROMFactorization
