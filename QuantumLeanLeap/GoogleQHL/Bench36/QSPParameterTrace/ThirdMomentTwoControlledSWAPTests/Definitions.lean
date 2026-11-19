import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.Kronecker


namespace QuantumLeanLeap.GoogleQHL.Bench36.ThirdMomentTwoControlledSWAPTests

noncomputable section

abbrev Qubit := Fin 2

abbrev ThreeRegs (H : Type*) := (H × H) × H

abbrev TotalRegs (H : Type*) := (Qubit × Qubit) × ThreeRegs H

@[nolint unusedArguments]
def plusKet : Qubit → ℂ :=
  fun _ => ((1 / Real.sqrt 2 : ℝ) : ℂ)

def ketbra {ι : Type*} (ψ φ : ι → ℂ) : Matrix ι ι ℂ :=
  fun a b => ψ a * star (φ b)

def plusProj : Matrix Qubit Qubit ℂ := ketbra plusKet plusKet

def pauliX : Matrix Qubit Qubit ℂ := !![0, 1; 1, 0]

@[nolint unusedArguments]
def sigmaIn {H : Type*} [Fintype H] [DecidableEq H]
    (ρ : Matrix H H ℂ) : Matrix (TotalRegs H) (TotalRegs H) ℂ :=
  Matrix.kronecker
    (Matrix.kronecker plusProj plusProj)
    (Matrix.kronecker (Matrix.kronecker ρ ρ) ρ)

def swap12 {H : Type*} [DecidableEq H] :
    Matrix (ThreeRegs H) (ThreeRegs H) ℂ :=
  fun x y =>
    if x.1.1 = y.1.2 ∧ x.1.2 = y.1.1 ∧ x.2 = y.2 then 1 else 0

def swap13 {H : Type*} [DecidableEq H] :
    Matrix (ThreeRegs H) (ThreeRegs H) ℂ :=
  fun x y =>
    if x.1.1 = y.2 ∧ x.1.2 = y.1.2 ∧ x.2 = y.1.1 then 1 else 0

def controlledSwapA1 {H : Type*} [DecidableEq H]
    (S : Matrix (ThreeRegs H) (ThreeRegs H) ℂ) :
    Matrix (TotalRegs H) (TotalRegs H) ℂ :=
  fun r c =>
    if r.1.2 = c.1.2 then
      if r.1.1 = (0 : Qubit) ∧ c.1.1 = (0 : Qubit) ∧ r.2 = c.2 then 1
      else if r.1.1 = (1 : Qubit) ∧ c.1.1 = (1 : Qubit) then S r.2 c.2
      else 0
    else 0

def controlledSwapA2 {H : Type*} [DecidableEq H]
    (S : Matrix (ThreeRegs H) (ThreeRegs H) ℂ) :
    Matrix (TotalRegs H) (TotalRegs H) ℂ :=
  fun r c =>
    if r.1.1 = c.1.1 then
      if r.1.2 = (0 : Qubit) ∧ c.1.2 = (0 : Qubit) ∧ r.2 = c.2 then 1
      else if r.1.2 = (1 : Qubit) ∧ c.1.2 = (1 : Qubit) then S r.2 c.2
      else 0
    else 0

def sigmaOut {H : Type*} [Fintype H] [DecidableEq H]
    (ρ : Matrix H H ℂ) : Matrix (TotalRegs H) (TotalRegs H) ℂ :=
  let U1 := controlledSwapA1 (swap12 : Matrix (ThreeRegs H) (ThreeRegs H) ℂ)
  let U2 := controlledSwapA2 (swap13 : Matrix (ThreeRegs H) (ThreeRegs H) ℂ)
  U2 * U1 * sigmaIn ρ * U1.conjTranspose * U2.conjTranspose

@[nolint unusedArguments]
def XXObservable {H : Type*} [Fintype H] [DecidableEq H] :
    Matrix (TotalRegs H) (TotalRegs H) ℂ :=
  Matrix.kronecker
    (Matrix.kronecker pauliX pauliX)
    (1 : Matrix (ThreeRegs H) (ThreeRegs H) ℂ)

end

end QuantumLeanLeap.GoogleQHL.Bench36.ThirdMomentTwoControlledSWAPTests
