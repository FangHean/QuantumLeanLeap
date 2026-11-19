import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup


namespace QuantumLeanLeap.GoogleQHL.Bench36.FirstOrderLieTrotterGlobalErrorScaling

noncomputable section
open scoped BigOperators
variable {d : ℕ}

def S1 (expm : Operator d → Operator d)
    (A B : Operator d) (τ : ℝ) :
    Operator d :=
  expm ((-Complex.I * (τ : ℂ)) • A) * expm ((-Complex.I * (τ : ℂ)) • B)

def commutator (A B : Operator d) : Operator d :=
  A * B - B * A

end

end QuantumLeanLeap.GoogleQHL.Bench36.FirstOrderLieTrotterGlobalErrorScaling
