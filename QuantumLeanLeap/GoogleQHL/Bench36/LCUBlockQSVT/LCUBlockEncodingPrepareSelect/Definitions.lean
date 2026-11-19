import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/




namespace QuantumLeanLeap.GoogleQHL.Bench36.LCUBlockEncodingPrepareSelect

noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36
open scoped BigOperators

variable {a n : ℕ} {L : Type*} [Fintype L] [DecidableEq L]

def weightedSum (αcoeff : L → ℝ)
    (U : L → Operator (2 ^ n)) : Operator (2 ^ n) :=
  ∑ ℓ, (αcoeff ℓ : ℂ) • U ℓ

def coeffSum (αcoeff : L → ℝ) : ℝ := ∑ ℓ, αcoeff ℓ

def selectOp (embed : L ↪ Fin (2 ^ a))
    (U : L → Operator (2 ^ n)) :
    Operator (2 ^ (a + n)) :=
  fun i j =>
    let (ia, is_) := prodEquiv.symm i
    let (ja, js) := prodEquiv.symm j
    ∑ ℓ, (if ia = embed ℓ then 1 else 0) *
      (if ja = embed ℓ then 1 else 0) * U ℓ is_ js

end

end QuantumLeanLeap.GoogleQHL.Bench36.LCUBlockEncodingPrepareSelect
