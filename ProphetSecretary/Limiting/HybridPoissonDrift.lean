import ProphetSecretary.Limiting.HybridResidualSplit
import ProphetSecretary.Limiting.HybridPotentialVerification

/-!
# Actual stopped Poisson drift of a finite potential

The constructed marked-Poisson compensator converts its reached premium into
the current-state intensity integral. All product and iterated integrability
obligations are proved before using this drift in the verification inequality.
-/

open MeasureTheory Set

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def HybridRule.poissonPotentialDrift (π : HybridRule n Seed) (Q : Model.Instance n)
    (κ : Measure ℝ) (μ : FiniteMeasure ℝ) (w c : ℝ) (q : HybridWorld n Seed × ℝ) : ℝ :=
  if q.2 ≤ π.realizedDuration q.1 then (μ : Measure ℝ).real univ *
    Model.positivePremium κ w (poissonContinuation Q w c q.1.2.2.1 q.2) else 0

lemma HybridRule.poissonPremium_expectation_eq_drift (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (Q P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ v, π.reachedPoissonPremium (designPoissonPremium Q κ w c) v ∂hybridWorldLaw P μ ν) =
      ∫ v, ∫ t, π.poissonPotentialDrift Q κ μ w c (v, t) ∂Model.Instance.uniformClock ∂hybridWorldLaw P μ ν := by
  have hB : 0 ≤ w * ∫ x, x ∂κ := mul_nonneg hw.le (integral_nonneg_of_ae hκ)
  have h := π.weighted_poisson_compensator_real_iterated hπ P μ ν (designPoissonPremium Q κ w c)
    (measurable_designPoissonPremium Q hQ κ hI hw hc) (designPoissonPremium_nonnegative Q κ w c)
      hB (designPoissonPremium_le Q hQ κ hκ hI hw.le hc)
  simpa only [designPoissonPremium, HybridRule.poissonPotentialDrift, integral_const, smul_eq_mul] using h

lemma HybridRule.integrable_poissonPotentialDrift (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (Q P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (π.poissonPotentialDrift Q κ μ w c) ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock) := by
  let F : Point × HybridWorld n Seed → ℝ := fun q => if q.1.1 ≤ π.realizedDuration q.2 then
    designPoissonPremium Q κ w c (q.1, q.2.2) else 0
  have hB : 0 ≤ w * ∫ x, x ∂κ := mul_nonneg hw.le (integral_nonneg_of_ae hκ)
  have hi : Integrable F ((intensity μ).prod (hybridWorldLaw P μ ν)) :=
    π.integrable_stoppedPoissonPremium hπ P μ ν (designPoissonPremium Q κ w c)
      (measurable_designPoissonPremium Q hQ κ hI hw hc) (designPoissonPremium_nonnegative Q κ w c)
        hB (designPoissonPremium_le Q hQ κ hκ hI hw.le hc)
  have hmp := measurePreserving_prodAssoc (hybridWorldLaw P μ ν) Model.Instance.uniformClock (μ : Measure ℝ)
  have hs : Integrable (fun q : (HybridWorld n Seed × ℝ) × ℝ => F ((q.1.2, q.2), q.1.1))
      (((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock).prod (μ : Measure ℝ)) :=
    hmp.integrable_comp_of_integrable hi.swap
  have hpart := hs.integral_prod_left
  have he : (fun q : HybridWorld n Seed × ℝ => ∫ x, F ((q.2, x), q.1) ∂(μ : Measure ℝ)) =
      π.poissonPotentialDrift Q κ μ w c := by
    funext q
    dsimp only [F]
    by_cases hq : q.2 ≤ π.realizedDuration q.1
    · simp only [hq, if_true, designPoissonPremium, integral_const, smul_eq_mul, HybridRule.poissonPotentialDrift]
    · simp only [hq, if_false, integral_zero, HybridRule.poissonPotentialDrift]
  rw [he] at hpart
  exact hpart

lemma HybridRule.expected_designResidual_eq_drift (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (Q P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ v, π.designResidual Q P κ hκ w c v ∂hybridWorldLaw P μ ν) =
      (∫ v, π.retainedDesignResidual Q P w c v ∂hybridWorldLaw P μ ν) -
      ∫ v, ∫ t, π.poissonPotentialDrift Q κ μ w c (v, t) ∂Model.Instance.uniformClock ∂hybridWorldLaw P μ ν := by
  have hr := π.integrable_retainedDesignResidual hπ Q P hQ hP κ hκ hI μ ν hw hc
  have hp := π.integrable_reachedPoissonPremium hπ P μ ν (designPoissonPremium Q κ w c)
    (measurable_designPoissonPremium Q hQ κ hI hw hc) (designPoissonPremium_le Q hQ κ hκ hI hw.le hc)
  calc
    _ = ∫ v, π.retainedDesignResidual Q P w c v - π.reachedPoissonPremium (designPoissonPremium Q κ w c) v
        ∂hybridWorldLaw P μ ν := integral_congr_ae (Filter.Eventually.of_forall
          (π.designResidual_eq_split Q P hQ κ hκ hw.le hc))
    _ = _ := by rw [integral_sub hr hp, π.poissonPremium_expectation_eq_drift hπ Q P hQ κ hκ hI μ ν hw hc]

end ProphetSecretary.Limiting
