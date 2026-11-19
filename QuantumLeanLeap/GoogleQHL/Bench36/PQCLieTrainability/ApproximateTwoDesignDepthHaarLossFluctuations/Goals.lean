import QuantumLeanLeap.GoogleQHL.Bench36.PQCLieTrainability.ApproximateTwoDesignDepthHaarLossFluctuations.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.ApproximateTwoDesignDepthHaarLossFluctuations
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0 (n : ℕ) (hn : 0 < n)

    (γ ε : ℝ)
    (hγ_pos : 0 < γ) (hγ_lt : γ < 1)
    (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (L : ℕ)

    (h_depth : (L : ℝ) ≥ Real.log (1 / ε) / Real.log (1 / (1 - γ)))

    (c : ℝ) (hc_pos : 0 < c)
    (p : ℕ → ℝ) (hp_pos : 0 < p n) (hp_gap : γ ≥ 1 / p n)

    (O : Matrix (Fin (N n)) (Fin (N n)) ℂ)
    (hO_sa : IsSelfAdjoint O)
    (hO_traceless : Matrix.trace O = 0)
    (hO_sq_bound : (Matrix.trace (O * O)).re ≤ (N n : ℝ))

    (hO_sq_real : (Matrix.trace (O * O)).im = 0)
    (ρ : Matrix (Fin (N n)) (Fin (N n)) ℂ)
    (hρ_sa : IsSelfAdjoint ρ)
    (hρ_trace : Matrix.trace ρ = 1)

    (hρ_pure : ρ * ρ = ρ)

    (haarExpect : (Matrix (Fin (N n)) (Fin (N n)) ℂ → ℂ) → ℂ)
    (haarVar : (Matrix (Fin (N n)) (Fin (N n)) ℂ → ℂ) → ℝ)

    (h_var_def : ∀ f : Matrix (Fin (N n)) (Fin (N n)) ℂ → ℂ,
      (haarVar f : ℂ) =
        haarExpect (fun U => f U * starRingEnd ℂ (f U)) -
          haarExpect f * starRingEnd ℂ (haarExpect f))
    (h_var_nonneg : ∀ f, 0 ≤ haarVar f)

    (h_haar_first_moment :
      ∀ (M A : Matrix (Fin (N n)) (Fin (N n)) ℂ),
        haarExpect (fun U =>
          Matrix.trace (U * M * U.conjTranspose * A)) =
          Matrix.trace M / (↑(N n) : ℂ) * Matrix.trace A)

    (h_loss_real :
      ∀ U : Matrix (Fin (N n)) (Fin (N n)) ℂ,
        starRingEnd ℂ (lossFunction U ρ O) = lossFunction U ρ O)

    (h_haar_second_moment :
      haarExpect (fun U =>
        lossFunction U ρ O * lossFunction U ρ O) =
        Matrix.trace (O * O) /
          ((↑(N n) : ℂ) * ((↑(N n) : ℂ) + 1))) : Prop :=
  (1 - γ) ^ L ≤ ε ∧

    (∃ K : ℝ, 0 < K ∧
      ∀ L' : ℕ, (L' : ℝ) ≥ K * p n * Real.log (↑n) →
        (1 - γ) ^ L' ≤ (↑n : ℝ) ^ (-c)) ∧

    haarExpect (fun U => lossFunction U ρ O) = 0 ∧

    haarVar (fun U => lossFunction U ρ O) =
      (Matrix.trace (O * O)).re /
        ((↑(N n) : ℝ) * ((↑(N n) : ℝ) + 1)) ∧

    haarVar (fun U => lossFunction U ρ O) ≤
      1 / ((↑(N n) : ℝ) + 1) ∧

    Real.sqrt (haarVar (fun U => lossFunction U ρ O)) ≤
      1 / Real.sqrt ((↑(N n) : ℝ) + 1)

end
end QuantumLeanLeap.GoogleQHL.Bench36.ApproximateTwoDesignDepthHaarLossFluctuations
