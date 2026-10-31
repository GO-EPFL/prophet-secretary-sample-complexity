import ProphetSecretary.Model.StandbyIidBenchmark
import ProphetSecretary.Model.JackpotMoments

/-! # A rational three-point competitive-ratio witness
There are thirty iid offers with a single fixed marginal, plus a deterministic
standby `4/5`. Each marginal has mass `1/90` at `7/5` and mass `1/3000000` at
`100000`; the remaining mass is at zero.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model.NumericalCompetitiveBound

noncomputable def mediumProbability : unitInterval :=
  ⟨(100000 : ℝ) / 8999997, by norm_num, by norm_num⟩
noncomputable def jackpotProbability : unitInterval :=
  ⟨(1 : ℝ) / 3000000, by norm_num, by norm_num⟩

noncomputable def marginal : Measure ℝ :=
  jackpotLaw (jackpotLaw (Measure.dirac 0) mediumProbability (7 / 5)) jackpotProbability 100000

instance marginal_probability : IsProbabilityMeasure marginal := by unfold marginal; infer_instance

lemma marginal_nonnegative : ∀ᵐ x ∂marginal, 0 ≤ x :=
  jackpotLaw_nonnegative _ (jackpotLaw_nonnegative _ (by simp) mediumProbability (by norm_num)) jackpotProbability (by norm_num)

lemma marginal_integrable (f : ℝ → ℝ) : Integrable f marginal :=
  jackpotLaw_integrable (jackpotLaw_integrable (integrable_dirac (by simp)) mediumProbability (7 / 5)) jackpotProbability 100000

lemma integral_marginal (f : ℝ → ℝ) :
    (∫ x, f x ∂marginal) = (1 / 90 : ℝ) * f (7 / 5) +
      (1 / 3000000 : ℝ) * f 100000 + (1 - 1 / 90 - 1 / 3000000 : ℝ) * f 0 := by
  unfold marginal
  rw [integral_jackpotLaw (jackpotLaw_integrable (integrable_dirac (by simp)) mediumProbability (7 / 5)),
    integral_jackpotLaw (integrable_dirac (by simp)), integral_dirac]
  norm_num [mediumProbability, jackpotProbability]
  ring

lemma marginalMaximum_eq (v : ℝ) : marginalMaximum marginal v =
    (1 / 90 : ℝ) * max (7 / 5) v + (1 / 3000000 : ℝ) * max 100000 v +
      (1 - 1 / 90 - 1 / 3000000 : ℝ) * max 0 v := integral_marginal _

lemma marginal_cdf_medium : marginal.real (Iio (7 / 5 : ℝ)) = 1 - 1 / 90 - 1 / 3000000 := by
  have h := integral_marginal ((Iio (7 / 5 : ℝ)).indicator (1 : ℝ → ℝ))
  rw [integral_indicator_one measurableSet_Iio] at h
  norm_num [Set.indicator, Pi.one_apply] at h ⊢
  exact h

lemma marginal_cdf_jackpot : marginal.real (Iio (100000 : ℝ)) = 1 - 1 / 3000000 := by
  have h := integral_marginal ((Iio (100000 : ℝ)).indicator (1 : ℝ → ℝ))
  rw [integral_indicator_one measurableSet_Iio] at h
  norm_num [Set.indicator, Pi.one_apply] at h ⊢
  exact h

noncomputable def witnessInstance : Instance 31 := standbyIidInstance marginal marginal_nonnegative (4 / 5) (by norm_num) 30

lemma instance_integrable : Integrable Instance.maximum witnessInstance.valuesLaw :=
  standbyIidInstance_integrable marginal marginal_nonnegative (marginal_integrable id) (4 / 5) (by norm_num) 30

lemma instance_expectedMaximum_lower : (1967 : ℝ) / 1000 ≤ witnessInstance.expectedMaximum := by
  have h := standbyIidInstance_expectedMaximum_ge_two_levels marginal marginal_nonnegative (marginal_integrable id)
    (a := (4 : ℝ) / 5) (b := (7 : ℝ) / 5) (J := 100000) (by norm_num) (by norm_num) (by norm_num) 30
  rw [marginal_cdf_medium, marginal_cdf_jackpot] at h
  apply le_trans _ h
  norm_num

end ProphetSecretary.Model.NumericalCompetitiveBound
