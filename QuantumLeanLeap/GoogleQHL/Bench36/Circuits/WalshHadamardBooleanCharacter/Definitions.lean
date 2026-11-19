import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Data.ZMod.Basic


namespace QuantumLeanLeap.GoogleQHL.Bench36.WalshHadamardBooleanCharacter

noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36
variable {n : ℕ}

abbrev BitReg (n : ℕ) := Fin n → Bool

def bitDot (s y : Fin n → Bool) : ZMod 2 :=
  ∑ j : Fin n, if s j && y j then (1 : ZMod 2) else 0

def booleanCharacter (s y : Fin n → Bool) : ℂ :=
  if bitDot s y = 0 then 1 else -1

def walshNorm (n : ℕ) : ℂ :=
  (Real.sqrt ((2 : ℝ) ^ n) : ℂ)⁻¹

def chiState (s : Fin n → Bool) : Vec (BitReg n) :=
  WithLp.toLp 2 fun y => walshNorm n * booleanCharacter s y

def boolToFin2 (b : Bool) : Fin (2 ^ 1) := if b then 1 else 0

def hadamardTensorOp : Mat (BitReg n) :=
  fun x y => ∏ i : Fin n,
    (H : Operator (2 ^ 1)) (boolToFin2 (x i)) (boolToFin2 (y i))

end

end QuantumLeanLeap.GoogleQHL.Bench36.WalshHadamardBooleanCharacter
