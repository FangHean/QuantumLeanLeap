import QuantumLeanLeap.GoogleQHL.Bench36.Foundation
/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic


namespace QuantumLeanLeap.GoogleQHL.Bench36.WeakFourierSamplingTranspositionSn

noncomputable section
open scoped BigOperators

abbrev SymmetricGroup (n : ℕ) := Equiv.Perm (Fin n)

def transposition12 (n : ℕ) (hn : 1 < n) : SymmetricGroup n :=
  Equiv.swap ⟨0, by omega⟩ ⟨1, hn⟩

def TV {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * Finset.sum Finset.univ (fun x => |P x - Q x|)

@[nolint unusedArguments]
def prodDist {α : Type*} [Fintype α] (P : α → ℝ) (m : ℕ) : (Fin m → α) → ℝ :=
  fun f => ∏ i : Fin m, P (f i)

end

end QuantumLeanLeap.GoogleQHL.Bench36.WeakFourierSamplingTranspositionSn
