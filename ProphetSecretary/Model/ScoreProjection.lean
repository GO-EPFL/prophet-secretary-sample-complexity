import ProphetSecretary.Model.Restriction
import Mathlib.Probability.HasLaw

/-!
# Complete-vector score expectations under causal identity projection

The score is an analytical function of the complete retained offer vector,
possibly including offers arriving after stopping. Its product integrability
is explicit. The actual product-law projection and causal `ignoreExtras`
execution transport its reward and duration expectations exactly.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace ProphetSecretary.Model.RandomizedPolicy
variable {n m : ℕ}

lemma ignoreExtras_score_reward (π : RandomizedPolicy m) (P : Instance n) (e : Fin m ↪ Fin n)
    (s : (Fin m → ℝ) → ℝ) (hs : Measurable s)
    (hInt : Integrable (fun ω : π.World => s ω.1*π.realizedReward ω) ((P.restrictBy e).worldLaw π.seedLaw)) :
    Integrable (fun ω : (π.ignoreExtras e).World => s (ω.1 ∘ e)*(π.ignoreExtras e).realizedReward ω) (P.worldLaw π.seedLaw) ∧
      (∫ ω : (π.ignoreExtras e).World, s (ω.1 ∘ e)*(π.ignoreExtras e).realizedReward ω ∂P.worldLaw π.seedLaw)=
        ∫ ω : π.World, s ω.1*π.realizedReward ω ∂(P.restrictBy e).worldLaw π.seedLaw := by
  have hMP := P.projectWorld_measurePreserving e π.seedLaw
  have hMeas : Measurable (fun ω : π.World => s ω.1*π.realizedReward ω) :=
    (hs.comp measurable_fst).mul π.measurable_realizedReward
  have hEq : (fun ω : (π.ignoreExtras e).World => s (ω.1 ∘ e)*(π.ignoreExtras e).realizedReward ω) =ᵐ[P.worldLaw π.seedLaw]
      (fun ω => s (Instance.projectWorld e ω).1*π.realizedReward (Instance.projectWorld e ω)) := by
    filter_upwards [P.world_clocks_distinct π.seedLaw] with ω hU
    have hR : (π.ignoreExtras e).realizedReward ω=π.realizedReward (Instance.projectWorld e ω) :=
      π.rule.ignoreExtras_reward e ω.2.2 ω.1 ω.2.1 (hU.comp e.injective)
    change s (ω.1 ∘ e)*(π.ignoreExtras e).realizedReward ω=s (ω.1 ∘ e)*π.realizedReward (Instance.projectWorld e ω)
    rw [hR]
  refine ⟨(hMP.integrable_comp_of_integrable hInt).congr hEq.symm,?_⟩
  exact (integral_congr_ae hEq).trans (hMP.hasLaw.integral_comp hMeas.aestronglyMeasurable)

lemma ignoreExtras_score_duration (π : RandomizedPolicy m) (P : Instance n) (e : Fin m ↪ Fin n)
    (s : (Fin m → ℝ) → ℝ) (hs : Measurable s)
    (hInt : Integrable (fun ω : π.World => s ω.1*π.realizedDuration ω) ((P.restrictBy e).worldLaw π.seedLaw)) :
    Integrable (fun ω : (π.ignoreExtras e).World => s (ω.1 ∘ e)*(π.ignoreExtras e).realizedDuration ω) (P.worldLaw π.seedLaw) ∧
      (∫ ω : (π.ignoreExtras e).World, s (ω.1 ∘ e)*(π.ignoreExtras e).realizedDuration ω ∂P.worldLaw π.seedLaw)=
        ∫ ω : π.World, s ω.1*π.realizedDuration ω ∂(P.restrictBy e).worldLaw π.seedLaw := by
  have hMP := P.projectWorld_measurePreserving e π.seedLaw
  have hMeas : Measurable (fun ω : π.World => s ω.1*π.realizedDuration ω) :=
    (hs.comp measurable_fst).mul π.measurable_realizedDuration
  have hEq : (fun ω : (π.ignoreExtras e).World => s (ω.1 ∘ e)*(π.ignoreExtras e).realizedDuration ω) =ᵐ[P.worldLaw π.seedLaw]
      (fun ω => s (Instance.projectWorld e ω).1*π.realizedDuration (Instance.projectWorld e ω)) := by
    exact Filter.Eventually.of_forall (fun ω => by
      have hT : (π.ignoreExtras e).realizedDuration ω=π.realizedDuration (Instance.projectWorld e ω) :=
        π.rule.ignoreExtras_stoppingTime e ω.2.2 ω.1 ω.2.1
      change s (ω.1 ∘ e)*(π.ignoreExtras e).realizedDuration ω=s (ω.1 ∘ e)*π.realizedDuration (Instance.projectWorld e ω)
      rw [hT])
  refine ⟨(hMP.integrable_comp_of_integrable hInt).congr hEq.symm,?_⟩
  exact (integral_congr_ae hEq).trans (hMP.hasLaw.integral_comp hMeas.aestronglyMeasurable)
end ProphetSecretary.Model.RandomizedPolicy
