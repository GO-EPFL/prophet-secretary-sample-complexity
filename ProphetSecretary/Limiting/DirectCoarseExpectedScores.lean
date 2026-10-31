import ProphetSecretary.Limiting.DirectCoarsePolicy
import ProphetSecretary.Probability.NormalizedScoreResponse

/-!
# Complete-score expectation transport for a direct coarse execution

A pointwise score identity on complete offer vectors is transported through
the actual causal identity projection. Integrability is preserved by its
product-law map. Scores do not appear in the callback's observation history.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {K n N : ℕ}

lemma directCoarsePolicy_expectedScores_of_pullback
    (P : Model.Instance n) (Q : Model.Instance N) (hKn : K≤n) (π : RandomizedHybridPolicy K) (d : ℝ)
    (s : (Fin (K+N) → ℝ) → ℝ) (hs : Measurable s) (h : Fin (n+N) → ℝ → ℝ)
    (hEq : ∀ x, s (x ∘ directCoarseEmbedding K n N hKn)=completeScore h x)
    (hRInt : Integrable (fun ω : (π.finiteCutoffEvaluation N d).World => s ω.1*(π.finiteCutoffEvaluation N d).realizedReward ω)
      (((P.restrictBy (Fin.castLEEmb hKn)).appendIndependent Q).worldLaw π.seedLaw))
    (hTInt : Integrable (fun ω : (π.finiteCutoffEvaluation N d).World => s ω.1*(π.finiteCutoffEvaluation N d).realizedDuration ω)
      (((P.restrictBy (Fin.castLEEmb hKn)).appendIndependent Q).worldLaw π.seedLaw)) :
    (directCoarsePolicy n N π d).expectedRewardScore (P.appendIndependent Q) h=
      (∫ ω : (π.finiteCutoffEvaluation N d).World, s ω.1*(π.finiteCutoffEvaluation N d).realizedReward ω
        ∂((P.restrictBy (Fin.castLEEmb hKn)).appendIndependent Q).worldLaw π.seedLaw) ∧
    (directCoarsePolicy n N π d).expectedDurationScore (P.appendIndependent Q) h=
      (∫ ω : (π.finiteCutoffEvaluation N d).World, s ω.1*(π.finiteCutoffEvaluation N d).realizedDuration ω
        ∂((P.restrictBy (Fin.castLEEmb hKn)).appendIndependent Q).worldLaw π.seedLaw) := by
  let e := directCoarseEmbedding K n N hKn
  let Γ := π.finiteCutoffEvaluation N d
  have hLaw := directCoarse_restricted_instance P Q hKn
  have hRInt' : Integrable (fun ω : Γ.World => s ω.1*Γ.realizedReward ω)
      (((P.appendIndependent Q).restrictBy e).worldLaw Γ.seedLaw) := by
    rw [hLaw]
    exact hRInt
  have hTInt' : Integrable (fun ω : Γ.World => s ω.1*Γ.realizedDuration ω)
      (((P.appendIndependent Q).restrictBy e).worldLaw Γ.seedLaw) := by
    rw [hLaw]
    exact hTInt
  have hR := Γ.ignoreExtras_score_reward (P.appendIndependent Q) e s hs hRInt'
  have hT := Γ.ignoreExtras_score_duration (P.appendIndependent Q) e s hs hTInt'
  have hRScore : (Γ.ignoreExtras e).expectedRewardScore (P.appendIndependent Q) h=
      ∫ ω : Γ.World, s ω.1*Γ.realizedReward ω ∂((P.restrictBy (Fin.castLEEmb hKn)).appendIndependent Q).worldLaw Γ.seedLaw := by
    exact (integral_congr_ae (Filter.Eventually.of_forall (fun ω =>
      congrArg (fun z => z*(Γ.ignoreExtras e).realizedReward ω) (hEq ω.1).symm))).trans
      (hR.2.trans (congrArg (fun A : Model.Instance (K+N) => ∫ ω : Γ.World, s ω.1*Γ.realizedReward ω ∂A.worldLaw Γ.seedLaw) hLaw))
  have hTScore : (Γ.ignoreExtras e).expectedDurationScore (P.appendIndependent Q) h=
      ∫ ω : Γ.World, s ω.1*Γ.realizedDuration ω ∂((P.restrictBy (Fin.castLEEmb hKn)).appendIndependent Q).worldLaw Γ.seedLaw := by
    exact (integral_congr_ae (Filter.Eventually.of_forall (fun ω =>
      congrArg (fun z => z*(Γ.ignoreExtras e).realizedDuration ω) (hEq ω.1).symm))).trans
      (hT.2.trans (congrArg (fun A : Model.Instance (K+N) => ∫ ω : Γ.World, s ω.1*Γ.realizedDuration ω ∂A.worldLaw Γ.seedLaw) hLaw))
  have hγ : directCoarsePolicy n N π d=Γ.ignoreExtras e := dif_pos hKn
  exact ⟨(congrArg (fun ρ : Model.RandomizedPolicy (n+N) => ρ.expectedRewardScore (P.appendIndependent Q) h) hγ).trans hRScore,
    (congrArg (fun ρ : Model.RandomizedPolicy (n+N) => ρ.expectedDurationScore (P.appendIndependent Q) h) hγ).trans hTScore⟩
end ProphetSecretary.Limiting
