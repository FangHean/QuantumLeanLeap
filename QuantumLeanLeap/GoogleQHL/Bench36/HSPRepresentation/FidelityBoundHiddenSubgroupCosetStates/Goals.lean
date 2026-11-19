import QuantumLeanLeap.GoogleQHL.Bench36.HSPRepresentation.FidelityBoundHiddenSubgroupCosetStates.Definitions
namespace QuantumLeanLeap.GoogleQHL.Bench36.FidelityBoundHiddenSubgroupCosetStates
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators
variable (G : Type*) [Group G] [Finite G]

def obligation_0 {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G)
    (fidelity : (G → G → ℂ) → (G → G → ℂ) → ℝ)

    (h_fidelity_nonneg : 0 ≤ fidelity (rhoK G H) (rhoK G K))

    (h_fidelity_upper :
      (fidelity (rhoK G H) (rhoK G K)) ^ 2 ≤
        matTrace G (supportProjector G H) (rhoK G K))

    (h_coset_inner :
      ∀ g g' : G,
        vecInner G (cosetState G g H) (cosetState G g' K) =
          ((cosetOverlapFinset G g g' H K).card : ℂ) /
            Real.sqrt ((Nat.card H : ℝ) * (Nat.card K : ℝ)))

    (h_product_card :
      Nat.card {x : G // ∃ h ∈ H, ∃ k ∈ K, x = h * k} *
        subgroupInterCard G H K = Nat.card H * Nat.card K)

    (h_trace_bound :
      matTrace G (supportProjector G H) (rhoK G K) ≤
        (subgroupInterCard G H K : ℝ) / (Nat.card H : ℝ)) : Prop :=
  fidelity (rhoK G H) (rhoK G K) ≤
      Real.sqrt ((subgroupInterCard G H K : ℝ) / (Nat.card H : ℝ))

end
end QuantumLeanLeap.GoogleQHL.Bench36.FidelityBoundHiddenSubgroupCosetStates
