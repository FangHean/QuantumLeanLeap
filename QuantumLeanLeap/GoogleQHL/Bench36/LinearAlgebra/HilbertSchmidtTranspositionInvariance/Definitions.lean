import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace


namespace QuantumLeanLeap.GoogleQHL.Bench36.HilbertSchmidtTranspositionInvariance

noncomputable section

def hsInner {d : ℕ} (B C : Operator d) : ℂ :=
  Matrix.trace (B.conjTranspose * C)

def hsNorm {d : ℕ} (B : Operator d) : ℝ :=
  Real.sqrt (hsInner B B).re

end

end QuantumLeanLeap.GoogleQHL.Bench36.HilbertSchmidtTranspositionInvariance
