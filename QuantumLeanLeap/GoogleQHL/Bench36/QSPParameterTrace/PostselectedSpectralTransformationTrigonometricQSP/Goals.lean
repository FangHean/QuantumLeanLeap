import QuantumLeanLeap.GoogleQHL.Bench36.QSPParameterTrace.PostselectedSpectralTransformationTrigonometricQSP.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.PostselectedSpectralTransformationTrigonometricQSP
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0 {d L : ℕ}
    (U : Operator d)
    (hU : U.conjTranspose * U = 1)
    (c : ℤ → ℂ)
    (hP_bound : ∀ t : ℝ, Complex.normSq (trigPolynomial L c t) ≤ 1)
    (θ φ : ℕ → ℝ)
    (hW_amplitude : ∀ t : ℝ,
      scalarQSPCircuit L (fun i => gateA (θ i) (φ i)) t 0 0 =
        trigPolynomial L c t)
    (Upow : ℤ → Operator d)
    (hUpow_pos : ∀ m : ℤ, 0 ≤ m → Upow m = U ^ m.toNat)
    (hUpow_neg : ∀ m : ℤ, m < 0 → Upow m = U.conjTranspose ^ (-m).toNat) : Prop :=
  controlZeroBlock
        (spectralQSPCircuit L (fun i => gateA (θ i) (φ i)) U) =
      trigPolynomialOfMatrix L c Upow ∧

    ∀ ψ : Fin d → ℂ,
      matVec (trigPolynomialOfMatrix L c Upow) ψ ≠ 0 →
        normalized (matVec (controlZeroBlock
          (spectralQSPCircuit L (fun i => gateA (θ i) (φ i)) U)) ψ) =
        normalized (matVec (trigPolynomialOfMatrix L c Upow) ψ)

end
end QuantumLeanLeap.GoogleQHL.Bench36.PostselectedSpectralTransformationTrigonometricQSP
