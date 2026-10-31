import ProphetSecretary.Statistics.FinitePriorPilot
import ProphetSecretary.Statistics.PosteriorGapExperiment

/-!
# Posterior distance from the visible pilot

The quadratic scalar diameter estimate is an explicit premise here. Its
pointwise application uses the true instance only analytically; the pilot
and posterior use the visible training prefix. The resulting constants do
not depend on the number of variables or prior atoms.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n N : ℕ}

lemma integrable_trueNormalizedGap (F : FinitePrior n) (N : ℕ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1)
    {W : BaseWorld F N → ℝ} (hW : Measurable W) (hUnit : ∀ ω, W ω∈Icc (0 : ℝ) 1) :
    Integrable (fun ω => normalizedScalarGap (F.offerInstance ω.1) (W ω)) (F.law N) := by
  have hm : Measurable (fun ω : BaseWorld F N => normalizedScalarGap (F.offerInstance ω.1) (W ω)) :=
    measurable_countable_choice measurable_fst (fun θ =>
      (F.offerInstance θ).measurable_normalizedGap_of_weight
        ((F.offerInstance θ).integrable_maximum_of_bounded (hcap θ)) hW hUnit)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Eventually.of_forall (fun ω => by
    have h := (F.offerInstance ω.1).normalizedScalarGap_mem_unit (hcap ω.1) (hUnit ω)
    rw [Real.norm_eq_abs,abs_of_nonneg h.1]
    exact h.2)

/-- The low-first-moment movement estimate, conditional only on the displayed
pointwise diameter inequality and a true-gap bound for the visible pilot. -/
theorem posteriorPilotDistance_le_of_quadratic_diameter (F : FinitePrior n) (N k l : ℕ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1)
    {p : ValueArray n N → ℝ} (hp : Measurable p) (hpu : ∀ d, p d∈Icc (0 : ℝ) 1)
    {D Kc error : ℝ} (hD : 0≤D) (hKc : 0≤Kc)
    (hDiameter : ∀ θ (a b : ℝ), a∈Icc (0 : ℝ) 1 → b∈Icc (0 : ℝ) 1 →
      (a-b)^2≤D*(normalizedScalarGap (F.offerInstance θ) a+normalizedScalarGap (F.offerInstance θ) b))
    (hPilot : (∫ ω, normalizedScalarGap (F.offerInstance ω.1) (p (F.observe N 0 l ω)) ∂F.law N)≤
      Kc*(∑ θ : Fin F.size, (F.weight θ : ℝ)*minimumNormalizedScalarGap (F.offerInstance θ))+error) :
    (∫ ω, (F.posterior N 0 k ω-p (F.observe N 0 l ω))^2 ∂F.law N)≤
      D*(1+Kc)*F.expectedPosteriorGap N 0 k+D*error := by
  let W := fun ω : BaseWorld F N => F.boundedPosteriorFromObservation N 0 k (F.observe N 0 k ω)
  let Y := fun ω : BaseWorld F N => p (F.observe N 0 l ω)
  have hW : Measurable W := (F.measurable_boundedPosteriorFromObservation N 0 k).comp (F.measurable_observe N 0 k)
  have hY : Measurable Y := hp.comp (F.measurable_observe N 0 l)
  have hWU (ω) : W ω∈Icc (0 : ℝ) 1 := F.boundedPosteriorFromObservation_mem_unit N 0 k _
  have hYU (ω) : Y ω∈Icc (0 : ℝ) 1 := hpu _
  have hSq : Integrable (fun ω => (W ω-Y ω)^2) (F.law N) := by
    apply Integrable.of_bound ((hW.sub hY).pow_const 2).aestronglyMeasurable 1
    exact Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      apply (sq_le_one_iff_abs_le_one _).mpr
      change |W ω-Y ω|≤1
      exact abs_le.mpr ⟨by linarith only [(hWU ω).1,(hYU ω).2],by linarith only [(hWU ω).2,(hYU ω).1]⟩)
  have hGW := F.integrable_trueNormalizedGap N hcap hW hWU
  have hGY := F.integrable_trueNormalizedGap N hcap hY hYU
  have hPoint := integral_mono hSq ((hGW.add hGY).const_mul D)
    (fun ω => hDiameter ω.1 (W ω) (Y ω) (hWU ω) (hYU ω))
  rw [integral_const_mul] at hPoint
  simp only [Pi.add_apply] at hPoint
  rw [integral_add hGW hGY] at hPoint
  have hGap : (∫ ω, normalizedScalarGap (F.offerInstance ω.1) (W ω) ∂F.law N)=F.expectedPosteriorGap N 0 k :=
    F.integral_observedPosteriorGap_eq_expected N 0 k hcap
  rw [hGap] at hPoint
  have hPrior := F.expectedPosteriorGap_ge_mean_minimum N 0 k hcap
  have hPilot' : (∫ ω, normalizedScalarGap (F.offerInstance ω.1) (Y ω) ∂F.law N)≤
      Kc*F.expectedPosteriorGap N 0 k+error :=
    hPilot.trans (add_le_add_left (mul_le_mul_of_nonneg_left hPrior hKc) _)
  have hMean := mul_le_mul_of_nonneg_left (add_le_add_left hPilot' (F.expectedPosteriorGap N 0 k)) hD
  have hEq : (∫ ω, (F.posterior N 0 k ω-Y ω)^2 ∂F.law N)=
      ∫ ω, (W ω-Y ω)^2 ∂F.law N := by
    apply integral_congr_ae
    filter_upwards [F.boundedPosterior_observed_eq_ae N 0 k] with ω hω
    rw [show W ω=F.posterior N 0 k ω from hω]
  change (∫ ω, (F.posterior N 0 k ω-Y ω)^2 ∂F.law N)≤_
  rw [hEq]
  nlinarith only [hPoint,hMean]

end ProphetSecretary.Statistics.FinitePrior
