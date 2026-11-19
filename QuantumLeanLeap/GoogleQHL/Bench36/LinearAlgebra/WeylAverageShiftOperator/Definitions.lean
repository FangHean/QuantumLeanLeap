import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace


namespace QuantumLeanLeap.GoogleQHL.Bench36.WeylAverageShiftOperator

noncomputable section
open scoped BigOperators

def omega (d : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (d : ℂ))

@[nolint unusedArguments]
def clockZ {d : ℕ} [NeZero d] : Operator d :=
  Matrix.diagonal fun j => omega d ^ (j : ℕ)

@[nolint unusedArguments]
def shiftX {d : ℕ} [NeZero d] : Operator d :=
  fun a b => if a.val = (b.val + 1) % d then 1 else 0

def weylAverage {d : ℕ} [NeZero d]
    (U : Operator d) : Operator d :=
  (1 / (d : ℂ)) • ∑ j : Fin d, ∑ k : Fin d,
    clockZ ^ j.val * shiftX ^ k.val * U *
    (clockZ ^ j.val).conjTranspose * (shiftX ^ k.val).conjTranspose

end

end QuantumLeanLeap.GoogleQHL.Bench36.WeylAverageShiftOperator
