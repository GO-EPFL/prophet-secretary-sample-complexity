import ProphetSecretary.Limiting.BernoulliClockState

/-!
# Mean continuation error over independent virtual clocks

The original clock vector, physical time, candidate type and duration
coefficient are fixed before averaging virtual clocks. Uniform state error
and the actual unseen-fraction moment bound give an explicit error tending
to zero, independently of the retained dimension and duration coefficient.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def FiniteIntensityHybridInstance.bernoulliClockErrorBound
    (B : FiniteIntensityHybridInstance n) (w : ℝ) (j : ℕ) : ℝ :=
  B.bernoulliStateError w j+(w*(∫ x, x ∂(B.intensity : Measure ℝ)))*
    (1/Real.sqrt (bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j : ℝ))

lemma FiniteIntensityHybridInstance.bernoulliClockErrorBound_tendsto_zero
    (B : FiniteIntensityHybridInstance n) (w : ℝ) : Tendsto (B.bernoulliClockErrorBound w) atTop (𝓝 0) := by
  change Tendsto (fun j => B.bernoulliStateError w j+(w*(∫ x, x ∂(B.intensity : Measure ℝ)))*
    (1/Real.sqrt (bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j : ℝ))) atTop (𝓝 0)
  have hClock : Tendsto (fun j => 1/Real.sqrt (bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j : ℝ))
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (bernoulliMultiplicity_tendsto_atTop _))
  have h := (B.bernoulliStateError_tendsto_zero w).add
    (hClock.const_mul (w*(∫ x, x ∂(B.intensity : Measure ℝ))))
  simpa only [FiniteIntensityHybridInstance.bernoulliClockErrorBound,mul_zero,add_zero] using h

/-- Actual general-policy continuation values are compared, not values of a
restricted Markov class. Independence belongs to the constructed clock law. -/
theorem FiniteIntensityHybridInstance.bernoulliClockState_absoluteMean_le
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    (j : ℕ) (u : Fin n → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (candidate : Option (Fin n))
    {w d : ℝ} (hw : 0 < w) (hd : 0 ≤ d) :
    let rate := (B.intensity : Measure ℝ).real univ
    let q := bernoulliMultiplicity rate j
    let p := bernoulliProbability rate measureReal_nonneg j
    let Q := finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) p q
    (∫ z : Fin q → ℝ, |Model.optimalScalarValue (Q.restrictTo (virtualClockState u t candidate z)) w d-
      ((B.restrictIndividuals (retainedClockState u t candidate)).remainingHorizon (remainingTime t)).optimalScalarValue w d|
      ∂Model.Instance.clocksLaw q) ≤ B.bernoulliClockErrorBound w j := by
  dsimp only
  let rate := (B.intensity : Measure ℝ).real univ
  let q := bernoulliMultiplicity rate j
  let p := bernoulliProbability rate measureReal_nonneg j
  let Q := finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) p q
  let V := ((B.restrictIndividuals (retainedClockState u t candidate)).remainingHorizon (remainingTime t)).optimalScalarValue w d
  let M := ∫ x, x ∂(B.intensity : Measure ℝ)
  let F : (Fin q → ℝ) → ℝ := fun z => |Model.optimalScalarValue (Q.restrictTo (virtualClockState u t candidate z)) w d-V|
  let G : (Fin q → ℝ) → ℝ := fun z => B.bernoulliStateError w j+(w*M)*|(virtualUnseenCount t z : ℝ)/(q : ℝ)-(1-t)|
  have hPoint (z : Fin q → ℝ) : F z ≤ G z := B.bernoulliClockState_value_error ha hμ j u ht candidate z hw hd
  have hState : Measurable (virtualClockState (q := q) u t candidate) := measurable_virtualClockState u t candidate
  have hFMeas : Measurable F := continuous_abs.measurable.comp
    (((measurable_of_countable (fun S : Finset (Fin (n+q)) => Model.optimalScalarValue (Q.restrictTo S) w d)).comp hState).sub measurable_const)
  have hCI := integrable_virtualUnseenFraction_error (q := q) t
  have hGI : Integrable G (Model.Instance.clocksLaw q) := (integrable_const _).add (hCI.const_mul (w*M))
  have hFI : Integrable F (Model.Instance.clocksLaw q) := hGI.mono' hFMeas.aestronglyMeasurable
    (Eventually.of_forall fun z => by simpa only [F,Real.norm_eq_abs,abs_abs] using hPoint z)
  have hC : 0 ≤ w*M := mul_nonneg hw.le (integral_nonneg_of_ae (B.intensity_supported.mono fun _ hx => hx.1.le))
  change (∫ z, F z ∂Model.Instance.clocksLaw q) ≤ _
  calc
    _ ≤ ∫ z, G z ∂Model.Instance.clocksLaw q := integral_mono hFI hGI hPoint
    _ = B.bernoulliStateError w j+(w*M)*
        (∫ z : Fin q → ℝ, |(virtualUnseenCount t z : ℝ)/(q : ℝ)-(1-t)| ∂Model.Instance.clocksLaw q) := by
      rw [integral_add (integrable_const _) (hCI.const_mul _),integral_const_mul,integral_const]
      simp only [probReal_univ,one_smul]
    _ ≤ B.bernoulliClockErrorBound w j := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (virtualUnseenFraction_absoluteMean_le ht (bernoulliMultiplicity_positive rate j)) hC)

end ProphetSecretary.Limiting
