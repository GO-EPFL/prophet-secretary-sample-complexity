import ProphetSecretary.Statistics.PremiumMean
import ProphetSecretary.Probability.BernoulliSubsetIntegral

/-!
# The all-arrivals Bellman identity for scalar planning

Following every arrival, without stopping, telescopes the positive Bellman
premiums. Conditioning one clock and reflecting elapsed to remaining time
makes its child set an independent Bernoulli subset. These are analytical
expectations over complete clocks, not observations supplied to a policy.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model
open ProphetSecretary.Probability

variable {n : ℕ}

lemma Instance.integrable_clockPremium (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) : Integrable (fun u => Q.clockPremium w c u i) (Instance.clocksLaw n) := by
  apply Integrable.of_bound (Q.measurable_clockPremium hQ hw hc i).aestronglyMeasurable
    (w * ∫ x, x ∂Q.law i)
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg (Q.clockPremium_nonnegative w c u i)]
  exact positivePremium_le_firstMoment (Q.law i) (Q.integrable_maximum_iff.mp hQ i)
    (Q.nonnegative i) hw.le (Q.continuationAtArrival_nonnegative hQ hw.le hc _ u i)

noncomputable def Instance.plannerPremium (Q : Instance n) (w c : ℝ)
    (i : Fin n) (s : ℝ) (u : Fin n → ℝ) : ℝ :=
  positivePremium (Q.law i) w
    (Q.continuationValue (bernoulliSubset (Finset.univ.erase i) (fun _ => s) u) s w c)

lemma Instance.integral_clockPremium_eq_plannerPremium (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) :
    (∫ u, Q.clockPremium w c u i ∂Instance.clocksLaw n) =
      ∫ s, (∫ u, Q.plannerPremium w c i s u ∂Instance.clocksLaw n) ∂Instance.uniformClock := by
  let F : (Fin n → ℝ) → ℝ := fun u => Q.clockPremium w c u i
  have hF : Measurable F := Q.measurable_clockPremium hQ hw hc i
  have hFI : Integrable F (Instance.clocksLaw n) := Q.integrable_clockPremium hQ hw hc i
  have hp : MeasurePreserving (fun z : (Fin n → ℝ) × ℝ => Function.update z.1 i z.2)
      ((Instance.clocksLaw n).prod Instance.uniformClock) (Instance.clocksLaw n) :=
    measurePreserving_replaceCoordinate (fun _ : Fin n => Instance.uniformClock) i
  have hPI : Integrable (fun z : (Fin n → ℝ) × ℝ => F (Function.update z.1 i z.2))
      ((Instance.clocksLaw n).prod Instance.uniformClock) := hp.integrable_comp_of_integrable hFI
  have hmap := integral_map (μ := (Instance.clocksLaw n).prod Instance.uniformClock)
    hp.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hp.map_eq] at hmap
  have hfirst : (∫ u, F u ∂Instance.clocksLaw n) =
      ∫ t, (∫ u, F (Function.update u i t) ∂Instance.clocksLaw n) ∂Instance.uniformClock := by
    rw [hmap, integral_prod _ hPI]
    exact integral_integral_swap hPI
  change (∫ u, F u ∂Instance.clocksLaw n) = _
  rw [hfirst, ← integral_uniformClock_reflection
    (fun t => ∫ u, F (Function.update u i t) ∂Instance.clocksLaw n)]
  apply integral_congr_ae
  have hsupp : ∀ᵐ s ∂Instance.uniformClock, s ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  filter_upwards [hsupp] with s hs
  have hupd : Measurable (fun u : Fin n → ℝ => Function.update u i (1-s)) := by
    apply measurable_pi_lambda
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using (measurable_const : Measurable (fun _ : Fin n → ℝ => 1-s))
    · simpa only [Function.update_of_ne hji] using measurable_pi_apply j
  have hreflect := integral_map (μ := Instance.clocksLaw n)
    (clocks_reflection_measurePreserving n).measurable.aemeasurable
    (hF.comp hupd).aestronglyMeasurable
  rw [(clocks_reflection_measurePreserving n).map_eq] at hreflect
  calc
    (∫ u, F (Function.update u i (1-s)) ∂Instance.clocksLaw n) =
        ∫ u, F (Function.update (fun j => 1-u j) i (1-s)) ∂Instance.clocksLaw n := hreflect
    _ = ∫ u, Q.plannerPremium w c i s u ∂Instance.clocksLaw n := by
      apply integral_congr_ae
      filter_upwards [] with u
      unfold F Instance.clockPremium Instance.continuationAtArrival Instance.plannerPremium
      rw [Function.update_self, unseen_replaceClock_erase,
        otherUnseen_reflected_eq_bernoulliSubset]
      simp only [show 1-(1-s) = s by ring, max_eq_right hs.1]

/-- The clock-subset form of `alg:all-arrivals`, for every finite instance. -/
theorem Instance.scalarValue_allArrivals (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue Q w c = c + ∑ i : Fin n,
      ∫ s, (∫ u, Q.plannerPremium w c i s u ∂Instance.clocksLaw n) ∂Instance.uniformClock := by
  have hmean := Q.integral_unstoppedPremium hQ hw hc
  unfold Instance.unstoppedPremium at hmean
  rw [integral_finsetSum _ (fun i _ => Q.integrable_clockPremium hQ hw hc i)] at hmean
  have he := fun i => Q.integral_clockPremium_eq_plannerPremium hQ hw hc i
  simp_rw [he] at hmean
  linarith

/-- The explicit Bernoulli-subset form of the all-arrivals recursion. -/
theorem Instance.scalarValue_allArrivals_subsets (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue Q w c = c + ∑ i : Fin n,
      ∫ s, (∑ B ∈ (Finset.univ.erase i).powerset,
        s^B.card * (1-s)^((Finset.univ.erase i).card-B.card) *
          positivePremium (Q.law i) w (Q.continuationValue B s w c)) ∂Instance.uniformClock := by
  rw [Q.scalarValue_allArrivals hQ hw hc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  have hsupp : ∀ᵐ s ∂Instance.uniformClock, s ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  filter_upwards [hsupp] with s hs
  exact integral_bernoulliSubset_constant (Finset.univ.erase i) hs
    (fun B => positivePremium (Q.law i) w (Q.continuationValue B s w c))

/-- Physical remaining horizons multiply the duration coefficient. At horizon
zero the reward-only value is retained, as in `alg:all-arrivals`. -/
theorem Instance.scalarValue_allArrivals_horizon (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {u z : ℝ} (hu : 0 ≤ u) (hz : 0 ≤ z) :
    optimalScalarValue Q 1 (z*u) = z*u + ∑ i : Fin n,
      ∫ s, (∑ B ∈ (Finset.univ.erase i).powerset,
        s^B.card * (1-s)^((Finset.univ.erase i).card-B.card) *
          positivePremium (Q.law i) 1 (Q.continuationValue B (u*s) 1 z)) ∂Instance.uniformClock := by
  rw [Q.scalarValue_allArrivals_subsets hQ zero_lt_one (mul_nonneg hz hu)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with s
  apply Finset.sum_congr rfl
  intro B _
  have he : Q.continuationValue B s 1 (z*u) = Q.continuationValue B (u*s) 1 z := by
    unfold Instance.continuationValue
    congr 1
    ring
  rw [he]

end ProphetSecretary.Model
