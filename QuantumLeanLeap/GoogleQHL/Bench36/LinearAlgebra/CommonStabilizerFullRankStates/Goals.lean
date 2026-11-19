import QuantumLeanLeap.GoogleQHL.Bench36.LinearAlgebra.CommonStabilizerFullRankStates.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.CommonStabilizerFullRankStates
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0 {d : ℕ}
    (ρ σ W : Operator d)
    (r s : Fin d → ℝ)
    (rvec svec : Fin d → Fin d → ℂ)

    (hρ_density : IsHermitianTraceOne ρ)
    (hσ_density : IsHermitianTraceOne σ)
    (hρ_full : IsFullRank ρ)
    (hσ_full : IsFullRank σ)

    (hρ_spectrum : HasSpectralExpansion ρ r rvec)
    (hσ_spectrum : HasSpectralExpansion σ s svec)

    (hr_simple : SimpleSpectrum r)
    (hs_simple : SimpleSpectrum s)

    (h_cross : ∀ i j : Fin d, innerProd (rvec i) (svec j) ≠ 0)

    (hW_unitary : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hWρ : W * ρ * W.conjTranspose = ρ)
    (hWσ : W * σ * W.conjTranspose = σ) : Prop :=
  IsScalarUnitary W ∧

    (∀ V : Operator d,
      V ∈ Matrix.unitaryGroup (Fin d) ℂ →
        V * ρ * V.conjTranspose = ρ →
          V * σ * V.conjTranspose = σ →
            IsScalarUnitary V)

end
end QuantumLeanLeap.GoogleQHL.Bench36.CommonStabilizerFullRankStates
