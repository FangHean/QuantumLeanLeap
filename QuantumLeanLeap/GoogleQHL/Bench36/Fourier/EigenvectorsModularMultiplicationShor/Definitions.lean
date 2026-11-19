import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Data.ZMod.Basic


namespace QuantumLeanLeap.GoogleQHL.Bench36.EigenvectorsModularMultiplicationShor

noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36

abbrev FinReg (N : ℕ) := Fin N

variable {N : ℕ} [NeZero N]

def UxOp (x : ℕ) : Mat (FinReg N) :=
  fun i j => if i.val = ((x : ZMod N) * (j.val : ZMod N)).val then 1 else 0

def psiS (x r s : ℕ) : Vec (FinReg N) :=
  WithLp.toLp 2 fun j : Fin N =>
    (Real.sqrt (r : ℝ) : ℂ)⁻¹ *
    ∑ k ∈ Finset.range r,
      Complex.exp (-(2 * Real.pi * Complex.I) * (s : ℂ) * (k : ℂ) / (r : ℂ)) *
      if j.val = ((x : ZMod N) ^ k).val then 1 else 0

end

end QuantumLeanLeap.GoogleQHL.Bench36.EigenvectorsModularMultiplicationShor
