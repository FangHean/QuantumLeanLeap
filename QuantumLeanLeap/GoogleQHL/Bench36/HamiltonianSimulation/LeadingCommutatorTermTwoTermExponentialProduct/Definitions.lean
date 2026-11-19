import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace


namespace QuantumLeanLeap.GoogleQHL.Bench36.LeadingCommutatorTermTwoTermExponentialProduct

noncomputable section
open scoped BigOperators

def commutator {d : ℕ} (A B : Operator d) :
    Operator d :=
  A * B - B * A

def E12 {d : ℕ}
    (expm : Operator d → Operator d)
    (H1 H2 : Operator d) :
    Operator d :=
  expm H1 * expm H2 - expm (H1 + H2)

end

end QuantumLeanLeap.GoogleQHL.Bench36.LeadingCommutatorTermTwoTermExponentialProduct
