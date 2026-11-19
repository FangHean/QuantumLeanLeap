import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Trace


namespace QuantumLeanLeap.GoogleQHL.Bench36.SpectralProjectorsBooleanPhaseOracle

noncomputable section
open scoped BigOperators

def phaseOracle {n : ℕ} (f : (Fin n → Bool) → Bool) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.diagonal fun x => if f x then -1 else 1

def piPlus {n : ℕ} (f : (Fin n → Bool) → Bool) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  (1 / 2 : ℂ) • (1 + phaseOracle f)

def piMinus {n : ℕ} (f : (Fin n → Bool) → Bool) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  (1 / 2 : ℂ) • (1 - phaseOracle f)

def preimageOneCard {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  (Finset.univ.filter (fun x => f x = true)).card

end

end QuantumLeanLeap.GoogleQHL.Bench36.SpectralProjectorsBooleanPhaseOracle
