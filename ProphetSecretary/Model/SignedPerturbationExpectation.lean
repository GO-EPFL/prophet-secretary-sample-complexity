import ProphetSecretary.Model.SignedMaximumGain
import ProphetSecretary.Model.ValueStationarity

/-! # Averaging actual independent-sign perturbations
The online instance is pushed forward coordinate by coordinate. Its signs are
an independent finite product law. The fixed observer's linear response has
mean zero, while the prophet gains from every tied eligible maximum.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

noncomputable def Instance.signPerturbation (P : Instance n) {h : ℝ} (hh : 0 ≤ h)
    (σ : Fin n → Bool) : Instance n :=
  P.perturbValues (highSignPerturbation h σ) (highSignPerturbation_measurable h σ) hh
    (highSignPerturbation_bound h σ) (highSignPerturbation_support h σ)

lemma measurable_signedMaximum (h : ℝ) (σ : Fin n → Bool) :
    Measurable (fun x : Fin n → ℝ ↦ signedMaximum h x σ) := by
  apply Instance.measurable_maximum.comp
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i).add (measurable_const.mul
    ((highSignPerturbation_measurable h σ i).comp (measurable_pi_apply i)))

lemma Instance.integrable_signedMaximum (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    {h : ℝ} (hh : 0 ≤ h) (σ : Fin n → Bool) :
    Integrable (fun x : Fin n → ℝ ↦ signedMaximum h x σ) P.valuesLaw := by
  apply (hP.add (integrable_const h)).mono' (measurable_signedMaximum h σ).aestronglyMeasurable
  exact Eventually.of_forall (fun x ↦ by
    have hNon : 0 ≤ signedMaximum h x σ := Instance.maximum_nonnegative _
    rw [Real.norm_eq_abs, abs_of_nonneg hNon]
    apply Instance.maximum_le _ (add_nonneg (Instance.maximum_nonnegative x) hh)
    intro i
    have hb := mul_le_mul_of_nonneg_left (abs_le.mp (highSignPerturbation_bound h σ i (x i))).2 hh
    have hx := Instance.le_maximum x i
    linarith)

lemma Instance.signPerturbation_expectedMaximum (P : Instance n) {h : ℝ} (hh : 0 ≤ h) (σ : Fin n → Bool) :
    (P.signPerturbation hh σ).expectedMaximum = ∫ x, signedMaximum h x σ ∂P.valuesLaw := by
  let ψ := highSignPerturbation h σ
  have hm := P.mapValues_measurePreserving (fun i x ↦ x + h * ψ i x)
    (fun i ↦ measurable_id.add (measurable_const.mul (highSignPerturbation_measurable h σ i)))
    (fun i ↦ (P.nonnegative i).mono (fun _ hx ↦ perturbation_nonnegative_of_support ψ hh
      (highSignPerturbation_bound h σ) (highSignPerturbation_support h σ) i hx))
  have he := integral_map (μ := P.valuesLaw) hm.measurable.aemeasurable Instance.measurable_maximum.aestronglyMeasurable
  rw [hm.map_eq] at he
  exact he

lemma RandomizedPolicy.selectedResponse_sign_mean_zero (π : RandomizedPolicy n) (P : Instance n) (h : ℝ) :
    (∫ σ, π.selectedResponse P (highSignPerturbation h σ) ∂fairSigns n) = 0 := by
  apply integral_fairSigns_odd
  intro σ
  rw [highSignPerturbation_reverse, π.selectedResponse_neg]

/-- Expected prophet gain from the complete tied-maximum event. Zero maxima
are harmless; the theorem needs no positive benchmark hypothesis. -/
theorem Instance.mean_signPerturbation_expectedMaximum_lower (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {h : ℝ} (hh : 0 ≤ h) :
    P.expectedMaximum + (h / 2) * P.valuesLaw.real {x : Fin n → ℝ | MaximumTiedAtLeast (2 * h) x} ≤
      ∫ σ, (P.signPerturbation hh σ).expectedMaximum ∂fairSigns n := by
  let E := {x : Fin n → ℝ | MaximumTiedAtLeast (2 * h) x}
  have hE : MeasurableSet E := measurableSet_maximumTiedAtLeast (2 * h)
  have hIndicator : Integrable (E.indicator (1 : (Fin n → ℝ) → ℝ)) P.valuesLaw := (integrable_const 1).indicator hE
  have hMean := integrable_integral_fairSigns P.valuesLaw (fun σ x ↦ signedMaximum h x σ)
    (fun σ ↦ P.integrable_signedMaximum hP hh σ)
  have hI := integral_mono (hP.add (hIndicator.const_mul (h / 2))) hMean
    (fun x ↦ by simpa only [E, Set.indicator, Set.mem_setOf_eq, Pi.one_apply, Pi.add_apply] using mean_signedMaximum_tie_gain hh x)
  simp only [Pi.add_apply] at hI
  rw [integral_add (f := fun x : Fin n → ℝ ↦ Instance.maximum x)
      (g := fun x ↦ (h / 2) * E.indicator 1 x) hP (hIndicator.const_mul (h / 2)),
    integral_const_mul, integral_indicator_one hE] at hI
  change P.expectedMaximum + h / 2 * P.valuesLaw.real E ≤ _ at hI
  apply hI.trans_eq
  rw [← integral_fairSigns_integral_swap P.valuesLaw (fun σ x ↦ signedMaximum h x σ)
    (fun σ ↦ P.integrable_signedMaximum hP hh σ)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun σ ↦ (P.signPerturbation_expectedMaximum hh σ).symm)

end ProphetSecretary.Model
