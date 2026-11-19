import QuantumLeanLeap.GoogleQHL.Bench36.HSPRepresentation.WeakFourierSamplingTranspositionSn.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.WeakFourierSamplingTranspositionSn
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators

def obligation_0 {irreps : Type*} [Fintype irreps]
    (n : ℕ) (hn : 1 < n)
    (P_triv P_pi : irreps → ℝ)
    (hP_triv_nn : ∀ x, 0 ≤ P_triv x)
    (hP_triv_sum : ∑ x, P_triv x = 1)
    (hP_pi_nn : ∀ x, 0 ≤ P_pi x)
    (hP_pi_sum : ∑ x, P_pi x = 1)
    (conjCard : ℕ)

    (h_conj_card_exact :
      conjCard = Nat.choose n 2 ∧ conjCard = n * (n - 1) / 2)

    (h_weak_fourier_bound :
      TV P_triv P_pi ≤ 1 / (2 * Real.sqrt (conjCard : ℝ))) : Prop :=
  conjCard = Nat.choose n 2 ∧
      conjCard = n * (n - 1) / 2 ∧

      TV P_triv P_pi ≤
        1 / Real.sqrt (2 * (n : ℝ) * ((n : ℝ) - 1)) ∧

      (∀ m : ℕ,
        TV (prodDist P_triv m) (prodDist P_pi m) ≤
          (m : ℝ) * TV P_triv P_pi) ∧

      (∀ advantage : ℝ, 0 < advantage →
        ∃ c : ℝ, 0 < c ∧
          ∀ m : ℕ,
            advantage ≤ TV (prodDist P_triv m) (prodDist P_pi m) →
              c * (n : ℝ) ≤ (m : ℝ))

end
end QuantumLeanLeap.GoogleQHL.Bench36.WeakFourierSamplingTranspositionSn
