import QuantumLeanLeap.GoogleQHL.Bench36.Fourier.QPESuperpositionExactEigenvectors.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.QPESuperpositionExactEigenvectors
set_option linter.unusedVariables false
noncomputable section
open QuantumLeanLeap.GoogleQHL.Bench36

def obligation_0 {τ : Type} [Fintype τ] [DecidableEq τ]
    (U : Mat (TargetReg τ))
    (u1 u2 : Vec (TargetReg τ))
    (h_orthonormal :
      @inner ℂ _ _ u1 u1 = 1 ∧ @inner ℂ _ _ u2 u2 = 1 ∧ @inner ℂ _ _ u1 u2 = 0)
    (φ1 φ2 : ℝ)
    (h_eigen1 : applyVec U u1 =
      Complex.exp (2 * Real.pi * Complex.I * (φ1 : ℂ)) • u1)
    (h_eigen2 : applyVec U u2 =
      Complex.exp (2 * Real.pi * Complex.I * (φ2 : ℂ)) • u2)
    (n : ℕ) (N : ℕ) (hN : N = 2 ^ n)
    (k1 k2 : Fin N)

    (h_exact1 : (N : ℝ) * φ1 = (k1.val : ℝ))
    (h_exact2 : (N : ℝ) * φ2 = (k2.val : ℝ))
    (countIQFT : Mat (CountReg N))

    (h_iqft : countIQFT * countQFT N = 1)
    (QPE : Vec (TargetReg τ) →ₗ[ℂ]
           Vec (Fin N × τ))

    (h_qpe_on_eigen : ∀ (u : Vec (TargetReg τ)) (φ : ℝ),
      applyVec U u =
        Complex.exp (2 * Real.pi * Complex.I * (φ : ℂ)) • u →
      QPE u = iqftCountingFactor countIQFT (phaseRibbon N φ) u)
    (α β : ℂ)
    (h_norm : Complex.normSq α + Complex.normSq β = 1) : Prop :=
  (applyVec (countQFT N)
        (ket (ι := CountReg N) k1 : Vec (CountReg N)) =
      phaseRibbon N φ1 ∧
     applyVec (countQFT N)
        (ket (ι := CountReg N) k2 : Vec (CountReg N)) =
      phaseRibbon N φ2) ∧

    (QPE u1 = tensorKet k1 u1 ∧ QPE u2 = tensorKet k2 u2) ∧

    (QPE (α • u1 + β • u2) = α • tensorKet k1 u1 + β • tensorKet k2 u2)

end
end QuantumLeanLeap.GoogleQHL.Bench36.QPESuperpositionExactEigenvectors
