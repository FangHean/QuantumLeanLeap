import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/




namespace QuantumLeanLeap.GoogleQHL.Bench36.ProductStateFactorizationQFT8Ket3

noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36

def qft8 : Operator (2 ^ 3) :=
  fun y x =>
    (Real.sqrt 8 : ℂ)⁻¹ *
      Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℂ) * (y.val : ℂ)) / 8)

def bigEndian (b₂ b₁ b₀ : Fin 2) : Fin (2 ^ 3) :=
  ⟨4 * b₂.val + 2 * b₁.val + b₀.val, by omega⟩

def singleQubitPhase (α : ℝ) : Fin 2 → ℂ :=
  fun b => (Real.sqrt 2 : ℂ)⁻¹ *
    (if b = 0 then 1 else Complex.exp (2 * Real.pi * Complex.I * (α : ℂ)))

def factor2 : Fin 2 → ℂ := singleQubitPhase (1 / 2)

def factor1 : Fin 2 → ℂ := singleQubitPhase (3 / 4)

def factor0 : Fin 2 → ℂ := singleQubitPhase (3 / 8)

end

end QuantumLeanLeap.GoogleQHL.Bench36.ProductStateFactorizationQFT8Ket3
