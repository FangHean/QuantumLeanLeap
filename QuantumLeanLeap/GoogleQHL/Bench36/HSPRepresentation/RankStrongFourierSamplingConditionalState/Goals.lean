import QuantumLeanLeap.GoogleQHL.Bench36.HSPRepresentation.RankStrongFourierSamplingConditionalState.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.RankStrongFourierSamplingConditionalState
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators
variable {G V : Type*} [Group G] [Finite G] [Fintype V] [DecidableEq V]

def obligation_0 (H : Subgroup G)
    (σ : G → Matrix V V ℂ)
    (χ : G → ℂ)
    (dσ : ℕ)
    (rank : Matrix V V ℂ → ℂ)
    (h_rank_idem : ∀ P : Matrix V V ℂ, P * P = P → rank P = Matrix.trace P)
    (h_rank_smul : ∀ (c : ℂ) (A : Matrix V V ℂ), c ≠ 0 → rank (c • A) = rank A)

    (h_unitary : ∀ g : G,
      (σ g).conjTranspose * σ g = 1 ∧ σ g * (σ g).conjTranspose = 1)
    (h_rep_one : σ 1 = 1)
    (h_rep_mul : ∀ g h : G, σ (g * h) = σ g * σ h)

    (h_char : ∀ g : G, χ g = Matrix.trace (σ g))

    (h_irreducible : ∀ (P : Matrix V V ℂ),
      P.conjTranspose = P → P * P = P →
        (∀ g : G, σ g * P = P * σ g) →
        P = 0 ∨ P = 1)
    (h_dim : Nat.card V = dσ)
    (h_char_sum_ne : charSumStar H χ ≠ 0) : Prop :=
  IsOrthogonalProjectorOnto (P_H_sigma H σ) (IsHInvariant H σ) ∧

      rhoHat H σ χ =
        (rank (P_H_sigma H σ))⁻¹ • (P_H_sigma H σ).conjTranspose ∧

      rank (rhoHat H σ χ) = rank (P_H_sigma H σ) ∧

      rank (P_H_sigma H σ) =
        (1 / (Nat.card H : ℂ)) * charSum H χ ∧

      rank (rhoHat H σ χ) =
        (1 / (Nat.card H : ℂ)) * charSumStar H χ

end
end QuantumLeanLeap.GoogleQHL.Bench36.RankStrongFourierSamplingConditionalState
