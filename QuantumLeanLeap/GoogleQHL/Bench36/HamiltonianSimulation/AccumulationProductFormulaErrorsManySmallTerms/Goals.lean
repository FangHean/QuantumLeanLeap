import QuantumLeanLeap.GoogleQHL.Bench36.HamiltonianSimulation.AccumulationProductFormulaErrorsManySmallTerms.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.AccumulationProductFormulaErrorsManySmallTerms
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators
variable {d : ℕ}

def obligation_0 (M : ℕ)
    (H F : ℕ → Operator d)
    (S : ℕ → Operator d)
    (E : Operator d)
    (opnorm : Operator d → ℝ)
    (expm : Operator d → Operator d)
    (h_opnorm_zero : opnorm 0 = 0)
    (h_opnorm_nonneg : ∀ A, 0 ≤ opnorm A)
    (h_opnorm_subadd : ∀ A B, opnorm (A + B) ≤ opnorm A + opnorm B)
    (h_opnorm_submul : ∀ A B, opnorm (A * B) ≤ opnorm A * opnorm B)
    (h_expm_zero : expm 0 = 1)
    (h_expm_bound : ∀ H, opnorm (expm H) ≤ Real.exp (opnorm H))
    (C γ R : ℝ)
    (h_C_nonneg : 0 ≤ C)
    (h_gamma_pos : 0 < γ)
    (h_gamma_lt_one : γ < 1)
    (h_R_pos : 0 < R)
    (h_bound_Mγ : (M : ℝ) * γ ≤ R)
    (h_hermitian : ∀ j ∈ Finset.Icc 1 M, IsSelfAdjoint (H j))
    (h_H_small : ∀ j ∈ Finset.Icc 1 M, opnorm (H j) ≤ γ)
    (h_S_zero : S 0 = 0)
    (h_S : ∀ k ∈ Finset.Icc 1 M, S k = partialSum H k)

    (h_local :
      ∀ k ∈ Finset.Icc 1 M,
        expm (S (k - 1)) * expm (H k) = expm (S k) + F k ∧
        opnorm (F k) ≤
          C * opnorm (S (k - 1)) * opnorm (H k) *
            Real.exp (opnorm (S (k - 1)) + opnorm (H k)))

    (h_error : orderedExpProduct M H expm = expm (S M) + E) : Prop :=
  opnorm E ≤ (C * Real.exp R / 2) * (M : ℝ) * ((M : ℝ) - 1) * γ ^ 2 ∧
      ∃ K : ℝ, 0 ≤ K ∧ opnorm E ≤ K * (M : ℝ) ^ 2 * γ ^ 2

end
end QuantumLeanLeap.GoogleQHL.Bench36.AccumulationProductFormulaErrorsManySmallTerms
