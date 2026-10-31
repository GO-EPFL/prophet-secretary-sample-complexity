import ProphetSecretary.Model.SignedPerturbationExpectation
import ProphetSecretary.Model.FirstMomentError
import ProphetSecretary.Model.HalfGuarantee

/-! # `upmom:ties`: tied positive maxima near criticality
Independent fair signs perturb each eligible variable. The fixed base policy's
linear response averages to zero. The global scalar inequality and quadratic
transport therefore bound the prophet's fair-sign gain, including its gain on
the full tied-maximum event.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

lemma Instance.signPerturbation_scalar_gain_mean_upper (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4) :
    optimalCompetitiveRatio * w *
      ((∫ σ, (P.signPerturbation hh.le σ).expectedMaximum ∂fairSigns n) - P.expectedMaximum) ≤
      scalarGap P w c + (32 / δ) * (1 + P.positiveCount) ^ 2 * h ^ 2 := by
  have hP := P.integrable_maximum_of_bounded hcap
  have hw : 0 < w := hδ.trans_le hwδ
  have hc : 0 < c := hδ.trans_le hcδ
  let π := P.valuePolicy hP hw.le hc.le
  let E := (32 / δ) * (1 + P.positiveCount) ^ 2 * h ^ 2
  let F := scalarGap P w c
  have hOne (σ : Fin n → Bool) :
      optimalCompetitiveRatio * w * ((P.signPerturbation hh.le σ).expectedMaximum - P.expectedMaximum) ≤
        (F + E) + w * h * π.selectedResponse P (highSignPerturbation h σ) := by
    have hQ := P.perturbValues_integrable_maximum hP (highSignPerturbation h σ)
      (highSignPerturbation_measurable h σ) hh.le (highSignPerturbation_bound h σ) (highSignPerturbation_support h σ)
    have hGlobal := globalScalar_inequality_of_integrable (P.signPerturbation hh.le σ) hQ hw.le hc.le
    have hTransport := (P.valuePerturbation_transport hcap hδ hwδ hcδ hsum hh hquarter
      (highSignPerturbation h σ) (highSignPerturbation_measurable h σ)
      (highSignPerturbation_bound h σ) (highSignPerturbation_support h σ)).2
    dsimp only [F, scalarGap, E]
    change optimalScalarValue (P.signPerturbation hh.le σ) w c - optimalScalarValue P w c -
      w * h * π.selectedResponse P (highSignPerturbation h σ) ≤ E at hTransport
    nlinarith only [hGlobal, hTransport]
  have hI := integral_mono (fairSigns_integrable _) (fairSigns_integrable _) hOne
  rw [integral_const_mul,
    integral_sub (f := fun σ ↦ (P.signPerturbation hh.le σ).expectedMaximum) (g := fun _ ↦ P.expectedMaximum)
      (fairSigns_integrable _) (integrable_const _),
    integral_add (f := fun _ : Fin n → Bool ↦ F + E)
      (g := fun σ ↦ w * h * π.selectedResponse P (highSignPerturbation h σ)) (integrable_const _)
      ((fairSigns_integrable _).const_mul (w * h)),
    integral_const_mul, π.selectedResponse_sign_mean_zero P h] at hI
  simpa only [integral_const, probReal_univ, one_smul, mul_zero, add_zero] using hI

/-- The complete finite statement of equation `upmom:ties`, with d_h explicit
through `valueStationarityError`. -/
theorem Instance.maximum_tie_probability_le (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4) :
    P.valuesLaw.real {x : Fin n → ℝ | MaximumTiedAtLeast (2 * h) x} ≤
      2 * P.valueStationarityError δ h w c / optimalCompetitiveRatio := by
  have hw : 0 < w := hδ.trans_le hwδ
  have hC : 0 < optimalCompetitiveRatio := (by norm_num : (0 : ℝ) < 1 / 2).trans_le half_le_optimalCompetitiveRatio
  have hLow := P.mean_signPerturbation_expectedMaximum_lower (P.integrable_maximum_of_bounded hcap) hh.le
  have hUp := P.signPerturbation_scalar_gain_mean_upper hcap hδ hwδ hcδ hsum hh hquarter
  have hScaled := mul_le_mul_of_nonneg_left hLow (mul_nonneg hC.le hw.le)
  have hMain : (optimalCompetitiveRatio * w * h) *
      P.valuesLaw.real {x : Fin n → ℝ | MaximumTiedAtLeast (2 * h) x} ≤
      2 * (scalarGap P w c + (32 / δ) * (1 + P.positiveCount) ^ 2 * h ^ 2) := by
    nlinarith only [hScaled, hUp]
  have hBound : P.valuesLaw.real {x : Fin n → ℝ | MaximumTiedAtLeast (2 * h) x} ≤
      2 * (scalarGap P w c + (32 / δ) * (1 + P.positiveCount) ^ 2 * h ^ 2) /
        (optimalCompetitiveRatio * w * h) := by
    apply (le_div_iff₀ (mul_pos (mul_pos hC hw) hh)).2
    nlinarith only [hMain]
  apply hBound.trans_eq
  unfold Instance.valueStationarityError
  field_simp [hC.ne', hw.ne', hh.ne', hδ.ne']


lemma firstMomentErrorFactor_ge_two_div_competitive (δ : ℝ) :
    2 / optimalCompetitiveRatio ≤ firstMomentErrorFactor δ :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- The common first-moment error controls the complete tied-maximum event. -/
theorem Instance.maximum_tie_probability_le_firstMomentError (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4) :
    P.valuesLaw.real {x : Fin n → ℝ | MaximumTiedAtLeast (2 * h) x} ≤ P.firstMomentError δ h w c := by
  have hD := P.valueStationarityError_nonnegative (P.integrable_maximum_of_bounded hcap)
    hδ hh.le (hδ.trans_le hwδ) (hδ.le.trans hcδ)
  have hE := firstMomentErrorFactor_ge_two_div_competitive δ
  have hE0 : 0 ≤ firstMomentErrorFactor δ := zero_le_one.trans (firstMomentErrorFactor_ge_one δ)
  have hL := P.tailCount_nonnegative 0
  have hExtra : 0 ≤ firstMomentErrorFactor δ * ((1 + P.positiveCount) * h) := by positivity
  calc
    _ ≤ 2 * P.valueStationarityError δ h w c / optimalCompetitiveRatio :=
      P.maximum_tie_probability_le hcap hδ hwδ hcδ hsum hh hquarter
    _ = (2 / optimalCompetitiveRatio) * P.valueStationarityError δ h w c := by ring
    _ ≤ firstMomentErrorFactor δ * P.valueStationarityError δ h w c := mul_le_mul_of_nonneg_right hE hD
    _ ≤ _ := by unfold Instance.firstMomentError; nlinarith only [hExtra]

end ProphetSecretary.Model
