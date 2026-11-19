import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.Notation


namespace QuantumLeanLeap.GoogleQHL.Bench36.LinearDependenceRvsFtwo

def v1R : Fin 3 → ℝ := ![1, 1, 0]

def v2R : Fin 3 → ℝ := ![0, 1, 1]

def v3R : Fin 3 → ℝ := ![1, 0, 1]

def v1F : Fin 3 → ZMod 2 := ![1, 1, 0]

def v2F : Fin 3 → ZMod 2 := ![0, 1, 1]

def v3F : Fin 3 → ZMod 2 := ![1, 0, 1]

def vectorFamilyR : Fin 3 → (Fin 3 → ℝ) := ![v1R, v2R, v3R]

def vectorFamilyF : Fin 3 → (Fin 3 → ZMod 2) := ![v1F, v2F, v3F]

end QuantumLeanLeap.GoogleQHL.Bench36.LinearDependenceRvsFtwo
