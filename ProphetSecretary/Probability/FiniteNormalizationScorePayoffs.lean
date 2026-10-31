import ProphetSecretary.Probability.FiniteNormalizationScores
import ProphetSecretary.Model.FiniteCanonicalBaseNormalization

/-!
# Exact fixed-policy score payoffs under positive normalization

The old policy's callbacks receive My and the corresponding transformed past.
The actual product-law change of variables preserves selected identities and
duration, and divides reward and maximum by M. The same identities hold on
every member of a perturbed law family while M and the base policy stay fixed.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

noncomputable def RandomizedPolicy.fixedBaseNormalizedPolicy (π : RandomizedPolicy n) (M : ℝ) : RandomizedPolicy n :=
  π.pullbackValues (M*·) (measurable_valueScale M)

lemma RandomizedPolicy.fixedBaseNormalizedPolicy_reward (π : RandomizedPolicy n) {M : ℝ}
    (hM : 0<M) (ω : π.World) :
    (π.fixedBaseNormalizedPolicy M).realizedReward (Instance.scaleWorld M⁻¹ ω)=M⁻¹*π.realizedReward ω := by
  have h := (π.rule.pullbackValues (M*·)).reward_scale_pullback M⁻¹ ω.2.2 Finset.univ ω.1 ω.2.1
  rw [π.rule.pullbackValues_scale_inverse M hM.ne'] at h
  exact h

lemma RandomizedPolicy.fixedBaseNormalizedPolicy_duration (π : RandomizedPolicy n) {M : ℝ}
    (hM : 0<M) (ω : π.World) :
    (π.fixedBaseNormalizedPolicy M).realizedDuration (Instance.scaleWorld M⁻¹ ω)=π.realizedDuration ω := by
  have h := (π.rule.pullbackValues (M*·)).pullbackValues_stoppingTime (M⁻¹*·) ω.2.2 Finset.univ ω.1 ω.2.1
  rw [π.rule.pullbackValues_scale_inverse M hM.ne'] at h
  exact h.symm

lemma RandomizedPolicy.fixedBaseNormalization_rewardScore (π : RandomizedPolicy n) (P : Instance n)
    {M : ℝ} (hM : 0<M) (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i)) :
    (π.fixedBaseNormalizedPolicy M).expectedRewardScore (P.scale M⁻¹ (inv_nonneg.mpr hM.le))
      (fixedBaseNormalizedScore M h)=M⁻¹*π.expectedRewardScore P h := by
  let ρ := π.fixedBaseNormalizedPolicy M
  let F := fun ω : ρ.World => completeScore (fixedBaseNormalizedScore M h) ω.1*ρ.realizedReward ω
  have hF : Measurable F :=
    ((measurable_completeScore (fixedBaseNormalizedScore_measurable M hh)).comp measurable_fst).mul ρ.measurable_realizedReward
  have hMP := P.scaleWorld_measurePreserving M⁻¹ (inv_nonneg.mpr hM.le) π.seedLaw
  have hMap := integral_map (μ:=P.worldLaw π.seedLaw) (f:=F) hMP.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hMP.map_eq] at hMap
  calc
    _ = ∫ ω : π.World, F (Instance.scaleWorld M⁻¹ ω) ∂P.worldLaw π.seedLaw := hMap
    _ = ∫ ω : π.World, M⁻¹*(completeScore h ω.1*π.realizedReward ω) ∂P.worldLaw π.seedLaw := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun ω => ?_)
      change completeScore (fixedBaseNormalizedScore M h) (fun i => M⁻¹*ω.1 i)*
        ρ.realizedReward (Instance.scaleWorld M⁻¹ ω)=_
      rw [completeScore_fixedBaseNormalizedScore hM,π.fixedBaseNormalizedPolicy_reward hM]
      ring
    _ = _ := by rw [integral_const_mul];rfl

lemma RandomizedPolicy.fixedBaseNormalization_durationScore (π : RandomizedPolicy n) (P : Instance n)
    {M : ℝ} (hM : 0<M) (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i)) :
    (π.fixedBaseNormalizedPolicy M).expectedDurationScore (P.scale M⁻¹ (inv_nonneg.mpr hM.le))
      (fixedBaseNormalizedScore M h)=π.expectedDurationScore P h := by
  let ρ := π.fixedBaseNormalizedPolicy M
  let F := fun ω : ρ.World => completeScore (fixedBaseNormalizedScore M h) ω.1*ρ.realizedDuration ω
  have hF : Measurable F :=
    ((measurable_completeScore (fixedBaseNormalizedScore_measurable M hh)).comp measurable_fst).mul ρ.measurable_realizedDuration
  have hMP := P.scaleWorld_measurePreserving M⁻¹ (inv_nonneg.mpr hM.le) π.seedLaw
  have hMap := integral_map (μ:=P.worldLaw π.seedLaw) (f:=F) hMP.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hMP.map_eq] at hMap
  calc
    _ = ∫ ω : π.World, F (Instance.scaleWorld M⁻¹ ω) ∂P.worldLaw π.seedLaw := hMap
    _ = _ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun ω => ?_)
      change completeScore (fixedBaseNormalizedScore M h) (fun i => M⁻¹*ω.1 i)*
        ρ.realizedDuration (Instance.scaleWorld M⁻¹ ω)=_
      rw [completeScore_fixedBaseNormalizedScore hM,π.fixedBaseNormalizedPolicy_duration hM]

lemma Instance.fixedBaseNormalization_maximumScore (P : Instance n) {M : ℝ} (hM : 0<M)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i)) :
    (P.scale M⁻¹ (inv_nonneg.mpr hM.le)).expectedMaximumScore (fixedBaseNormalizedScore M h)=
      M⁻¹*P.expectedMaximumScore h := by
  let F := fun x : Fin n → ℝ => completeScore (fixedBaseNormalizedScore M h) x*Instance.maximum x
  have hF : Measurable F := (measurable_completeScore (fixedBaseNormalizedScore_measurable M hh)).mul Instance.measurable_maximum
  have hMP := P.scaleValues_measurePreserving M⁻¹ (inv_nonneg.mpr hM.le)
  have hMap := integral_map (μ:=P.valuesLaw) (f:=F) hMP.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hMP.map_eq] at hMap
  calc
    _ = ∫ x, F (fun i => M⁻¹*x i) ∂P.valuesLaw := hMap
    _ = ∫ x, M⁻¹*(completeScore h x*Instance.maximum x) ∂P.valuesLaw := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun x => ?_)
      change completeScore (fixedBaseNormalizedScore M h) (fun i => M⁻¹*x i)*
        Instance.maximum (fun i => M⁻¹*x i)=_
      rw [completeScore_fixedBaseNormalizedScore hM,Instance.maximum_scale M⁻¹ (inv_nonneg.mpr hM.le)]
      ring
    _ = _ := by rw [integral_const_mul];rfl

end ProphetSecretary.Model
