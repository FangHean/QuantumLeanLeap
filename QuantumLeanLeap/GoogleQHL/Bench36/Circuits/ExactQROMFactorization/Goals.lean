import QuantumLeanLeap.GoogleQHL.Bench36.Circuits.ExactQROMFactorization.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.ExactQROMFactorization
set_option linter.unusedVariables false
noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36
variable {n m : ℕ}

def obligation_0 (D : (Fin n → Bool) → (Fin m → Bool)) (k : Fin n → Bool) : Prop :=
  (Ck D k : Mat (QReg n m))
      ∈ Matrix.unitaryGroup (QReg n m) ℂ

def obligation_1 (D : (Fin n → Bool) → (Fin m → Bool))
    (k x : Fin n → Bool) (y : Fin m → Bool) : Prop :=
  applyVec (Ck D k) (ket (x, y)) =
      if x = k then ket (k, boolFunXor y (D k)) else ket (x, y)

def obligation_2 (D : (Fin n → Bool) → (Fin m → Bool))
    (L : List (Fin n → Bool)) (hL : L.Nodup) (hL_all : ∀ k, k ∈ L) : Prop :=
  (L.map (Ck D)).prod = qromOracle D

def obligation_3 (D : (Fin n → Bool) → (Fin m → Bool))
    (k l : Fin n → Bool) : Prop :=
  Ck D k * Ck D l = Ck D l * Ck D k

end
end QuantumLeanLeap.GoogleQHL.Bench36.ExactQROMFactorization
