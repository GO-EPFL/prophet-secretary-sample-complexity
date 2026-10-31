import ProphetSecretary.Probability.LikelihoodRemainder
import ProphetSecretary.Model.ScalarObjectiveBounds

/-!
# Fixed online payoffs under likelihood tilts

Policy decisions, reward-duration coefficients and the independent auxiliary law are
held fixed. Bounds are almost sure under the base instance; absolute continuity
transfers them to the tilted law. No policy is reoptimized in these statements.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace ProphetSecretary.Model

namespace Instance

variable {n : ℕ}

lemma likelihoodTilt_bounded (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) (θ : ℝ) (hθ : |θ| ≤ 1 / 4)
    {H : ℝ} (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    ∀ i, ∀ᵐ x ∂(P.likelihoodTilt h hh hb hm θ hθ).law i, x ≤ H :=
  fun i => (ProphetSecretary.Probability.tiltLaw_absolutelyContinuous (P.law i) (h i) θ).ae_le (hbound i)

lemma values_bound_ae (P : Instance n) {H : ℝ} (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ H := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hbound i)

end Instance

namespace RandomizedPolicy

variable {n : ℕ}

lemma scalarPayoff_bound_ae (π : RandomizedPolicy n) (P : Instance n) {H w c : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    ∀ᵐ ω : π.World ∂P.worldLaw π.seedLaw,
      |w * π.realizedReward ω + c * π.realizedDuration ω| ≤ w * H + c := by
  have hp : MeasurePreserving (fun ω : π.World => ω.1) (P.worldLaw π.seedLaw) P.valuesLaw := measurePreserving_fst
  filter_upwards [hp.quasiMeasurePreserving.ae P.ae_nonnegative,
    hp.quasiMeasurePreserving.ae (P.values_bound_ae hbound), P.worldTime_mem_unitInterval π.seedLaw π.rule Finset.univ]
    with ω hx0 hxH ht
  have hR0 : 0 ≤ π.realizedReward ω := π.rule.reward_nonnegative _ _ _ _ hx0
  have hRH : π.realizedReward ω ≤ H :=
    (π.rule.reward_le_maximum _ _ _ _).trans (Instance.maximum_le _ hH hxH)
  have hT0 : 0 ≤ π.realizedDuration ω := ht.1
  have hT1 : π.realizedDuration ω ≤ 1 := ht.2
  rw [abs_of_nonneg (add_nonneg (mul_nonneg hw hR0) (mul_nonneg hc hT0))]
  exact add_le_add (mul_le_mul_of_nonneg_left hRH hw) (by simpa using mul_le_mul_of_nonneg_left hT1 hc)

lemma integrable_scalarPayoff_of_bounded (π : RandomizedPolicy n) (P : Instance n) {H w c : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (fun ω : π.World => w * π.realizedReward ω + c * π.realizedDuration ω) (P.worldLaw π.seedLaw) := by
  apply Integrable.of_bound ((measurable_const.mul π.measurable_realizedReward).add
    (measurable_const.mul π.measurable_realizedDuration)).aestronglyMeasurable (w * H + c)
  simpa only [Pi.add_apply, Pi.mul_apply, Real.norm_eq_abs] using π.scalarPayoff_bound_ae P hH hbound hw hc

lemma integrable_scalarScore_of_bounded (π : RandomizedPolicy n) (P : Instance n) {H w c : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (hw : 0 ≤ w) (hc : 0 ≤ c)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) :
    Integrable (fun ω : π.World => (w * π.realizedReward ω + c * π.realizedDuration ω) *
      ProphetSecretary.Probability.completeScore h ω.1) (P.worldLaw π.seedLaw) := by
  have hZ : Integrable (ProphetSecretary.Probability.completeScore h) P.valuesLaw := by
    simpa only [pow_one, Instance.valuesLaw] using ProphetSecretary.Probability.completeScore_integrable_pow P.law h hh hb 1
  have hp : MeasurePreserving (fun ω : π.World => ω.1) (P.worldLaw π.seedLaw) P.valuesLaw := measurePreserving_fst
  have hDom := (hp.integrable_comp_of_integrable hZ.abs).const_mul (w * H + c)
  apply hDom.mono' (((measurable_const.mul π.measurable_realizedReward).add
    (measurable_const.mul π.measurable_realizedDuration)).mul
      ((ProphetSecretary.Probability.measurable_completeScore hh).comp measurable_fst)).aestronglyMeasurable
  filter_upwards [π.scalarPayoff_bound_ae P hH hbound hw hc] with ω hω
  simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)

/-- Fixed-policy part of `upfish:curvature` and `lem:score-information`, with all
training/arrival randomness included in the fixed independent auxiliary law. -/
lemma scalarObjective_likelihood_taylor (π : RandomizedPolicy n) (P : Instance n)
    {H w c : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (hw : 0 ≤ w) (hc : 0 ≤ c)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂P.law i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    |π.scalarObjective (P.likelihoodTilt h hh hb hm θ hθ) w c - π.scalarObjective P w c -
      θ * (∫ ω : π.World, (w * π.realizedReward ω + c * π.realizedDuration ω) *
        ProphetSecretary.Probability.completeScore h ω.1 ∂P.worldLaw π.seedLaw)| ≤
          2 * (w * H + c) * θ ^ 2 * ProphetSecretary.Probability.information P.law h := by
  have hG : Measurable (fun ω : π.World => w * π.realizedReward ω + c * π.realizedDuration ω) :=
    (measurable_const.mul π.measurable_realizedReward).add (measurable_const.mul π.measurable_realizedDuration)
  have ht := ProphetSecretary.Probability.fixedPayoff_law_taylor_bound_prod P.law ((Instance.clocksLaw n).prod π.seedLaw)
    h hh hb hm _ hG (add_nonneg (mul_nonneg hw hH) hc) (π.scalarPayoff_bound_ae P hH hbound hw hc) hθ
  exact ht

lemma expectedReward_likelihood_taylor (π : RandomizedPolicy n) (P : Instance n) {H : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂P.law i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    |π.expectedReward (P.likelihoodTilt h hh hb hm θ hθ) - π.expectedReward P -
      θ * (∫ ω : π.World, π.realizedReward ω * ProphetSecretary.Probability.completeScore h ω.1 ∂P.worldLaw π.seedLaw)| ≤
        2 * H * θ ^ 2 * ProphetSecretary.Probability.information P.law h := by
  have ht := π.scalarObjective_likelihood_taylor P hH hbound zero_le_one (le_refl (0 : ℝ)) h hh hb hm hθ
  rw [π.scalarObjective_eq _ ((P.likelihoodTilt h hh hb hm θ hθ).integrable_maximum_of_bounded
      (P.likelihoodTilt_bounded h hh hb hm θ hθ hbound)),
    π.scalarObjective_eq P (P.integrable_maximum_of_bounded hbound)] at ht
  simpa only [one_mul, zero_mul, add_zero] using ht

/-- Duration is bounded independently of offer integrability or a value cap. -/
lemma expectedDuration_likelihood_taylor (π : RandomizedPolicy n) (P : Instance n)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂P.law i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    |π.expectedDuration (P.likelihoodTilt h hh hb hm θ hθ) - π.expectedDuration P -
      θ * (∫ ω : π.World, π.realizedDuration ω * ProphetSecretary.Probability.completeScore h ω.1 ∂P.worldLaw π.seedLaw)| ≤
        2 * θ ^ 2 * ProphetSecretary.Probability.information P.law h := by
  have hGb : ∀ᵐ ω : π.World ∂P.worldLaw π.seedLaw, |π.realizedDuration ω| ≤ 1 := by
    filter_upwards [P.worldTime_mem_unitInterval π.seedLaw π.rule Finset.univ] with ω ht
    simpa only [realizedDuration, abs_of_nonneg ht.1] using ht.2
  have ht := ProphetSecretary.Probability.fixedPayoff_law_taylor_bound_prod P.law ((Instance.clocksLaw n).prod π.seedLaw)
    h hh hb hm π.realizedDuration π.measurable_realizedDuration zero_le_one hGb hθ
  simpa only [one_mul, mul_one, expectedDuration, Instance.worldLaw, Instance.valuesLaw,
    Instance.likelihoodTilt, ProphetSecretary.Probability.productTiltLaw] using ht

end RandomizedPolicy

namespace Instance

variable {n : ℕ}

lemma maximumScore_integrable_of_bounded (P : Instance n) {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) :
    Integrable (fun x => maximum x * ProphetSecretary.Probability.completeScore h x) P.valuesLaw := by
  have hZ : Integrable (ProphetSecretary.Probability.completeScore h) P.valuesLaw := by
    simpa only [pow_one, Instance.valuesLaw] using ProphetSecretary.Probability.completeScore_integrable_pow P.law h hh hb 1
  apply (hZ.abs.const_mul H).mono' (measurable_maximum.mul (ProphetSecretary.Probability.measurable_completeScore hh)).aestronglyMeasurable
  filter_upwards [P.values_bound_ae hbound] with x hx
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (maximum_nonnegative x)]
  exact mul_le_mul_of_nonneg_right (maximum_le x hH hx) (abs_nonneg _)

/-- The maximum's Taylor estimate has the same information constant as a fixed payoff. -/
lemma expectedMaximum_likelihood_taylor (P : Instance n) {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    |(P.likelihoodTilt h hh hb hm θ hθ).expectedMaximum - P.expectedMaximum -
      θ * (∫ x, maximum x * ProphetSecretary.Probability.completeScore h x ∂P.valuesLaw)| ≤
        2 * H * θ ^ 2 * ProphetSecretary.Probability.information P.law h := by
  have hFb : ∀ᵐ x ∂P.valuesLaw, |maximum x| ≤ H :=
    (P.values_bound_ae hbound).mono fun x hx => by rw [abs_of_nonneg (maximum_nonnegative x)]; exact maximum_le x hH hx
  exact ProphetSecretary.Probability.fixedPayoff_law_taylor_bound P.law h hh hb hm maximum measurable_maximum hH hFb hθ

end Instance
end ProphetSecretary.Model
