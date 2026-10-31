import ProphetSecretary.Limiting.ContinuousWeightedMeasure

/-!
# The intensity above a reserve from a finite continuous-weight measure

Dividing by the positive ordering weight recovers a sigma-finite mark
intensity above the reserve. Weighted mass at or below the reserve is erased.
Every upper band is finite with its explicit reciprocal-weight bound.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting

noncomputable def reserveReciprocalWeight (w : ℝ →ᵇ ℝ) (a x : ℝ) : ENNReal :=
  if a < x then ENNReal.ofReal (1 / w x) else 0
lemma measurable_reserveReciprocalWeight (w : ℝ →ᵇ ℝ) (a : ℝ) :
    Measurable (reserveReciprocalWeight w a) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (measurable_const.div w.continuous.measurable).ennreal_ofReal measurable_const
noncomputable def reserveMarkIntensity (η : FiniteMeasure ℝ) (w : ℝ →ᵇ ℝ) (a : ℝ) : Measure ℝ :=
  (η : Measure ℝ).withDensity (reserveReciprocalWeight w a)
instance reserveMarkIntensity_sigmaFinite (η : FiniteMeasure ℝ) (w : ℝ →ᵇ ℝ) (a : ℝ) :
    SigmaFinite (reserveMarkIntensity η w a) := by
  apply SigmaFinite.withDensity_of_ne_top'
  intro x
  unfold reserveReciprocalWeight
  split_ifs <;> simp
lemma reserveMarkIntensity_below_zero (η : FiniteMeasure ℝ) (w : ℝ →ᵇ ℝ) (a : ℝ) :
    reserveMarkIntensity η w a (Iic a) = 0 := by
  rw [reserveMarkIntensity,withDensity_apply _ measurableSet_Iic]
  calc
    _ = ∫⁻ _x in Iic a, (0 : ENNReal) ∂(η : Measure ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      exact if_neg (not_lt.mpr hx)
    _ = 0 := by simp
lemma reserveMarkIntensity_supported_interval (η : FiniteMeasure ℝ) (w : ℝ →ᵇ ℝ) (a : ℝ)
    {H : ℝ} (hcap : (η : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) :
    reserveMarkIntensity η w a (Ioc a H)ᶜ = 0 := by
  have hbase : reserveMarkIntensity η w a (Icc (0 : ℝ) H)ᶜ = 0 :=
    (withDensity_absolutelyContinuous _ _) hcap
  have hzero := measure_union_null hbase (reserveMarkIntensity_below_zero η w a)
  apply measure_mono_null _ hzero
  intro x hx
  by_cases hpos : a < x
  · exact Or.inl (fun hmem => hx ⟨hpos,hmem.2⟩)
  · exact Or.inr (not_lt.mp hpos)

theorem reserveMarkIntensity_tail_le (η : FiniteMeasure ℝ) (w : ℝ →ᵇ ℝ) (a : ℝ)
    (hw : Monotone w) {b : ℝ} (hb : a < b) (hwb : 0 < w b) :
    reserveMarkIntensity η w a (Ioi b) ≤ ENNReal.ofReal ((η.mass : ℝ) / w b) := by
  rw [reserveMarkIntensity,withDensity_apply _ measurableSet_Ioi]
  have hbound : ∀ᵐ x ∂(η : Measure ℝ).restrict (Ioi b),
      reserveReciprocalWeight w a x ≤ ENNReal.ofReal (1 / w b) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [reserveReciprocalWeight,if_pos (hb.trans hx)]
    exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le hwb (hw hx.le))
  calc
    _ ≤ ∫⁻ _x in Ioi b, ENNReal.ofReal (1/w b) ∂(η : Measure ℝ) := lintegral_mono_ae hbound
    _ = ENNReal.ofReal (1/w b) * (η : Measure ℝ) (Ioi b) := by simp
    _ ≤ ENNReal.ofReal (1/w b) * (η : Measure ℝ) Set.univ :=
      mul_le_mul_of_nonneg_left (measure_mono (subset_univ _)) bot_le
    _ = ENNReal.ofReal ((η.mass : ℝ) / w b) := by
      rw [← FiniteMeasure.ennreal_mass,← ENNReal.ofReal_coe_nnreal,← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / w b)]
      congr 1
      ring

noncomputable def reserveMarkIntensityAbove (η : FiniteMeasure ℝ) (w : ℝ →ᵇ ℝ) (a b : ℝ)
    (hw : Monotone w) (hb : a < b) (hwb : 0 < w b) : FiniteMeasure ℝ :=
  ⟨(reserveMarkIntensity η w a).restrict (Ioi b),
    ⟨by simpa using (reserveMarkIntensity_tail_le η w a hw hb hwb).trans_lt ENNReal.ofReal_lt_top⟩⟩

lemma reserveMarkIntensityAbove_restrict (η : FiniteMeasure ℝ) (w : ℝ →ᵇ ℝ) (a : ℝ)
    (hw : Monotone w) {b c : ℝ} (hb : a < b) (hc : a < c)
    (hwb : 0 < w b) (hwc : 0 < w c) (hbc : b ≤ c) :
    (reserveMarkIntensityAbove η w a b hw hb hwb : Measure ℝ).restrict (Ioi c) =
      (reserveMarkIntensityAbove η w a c hw hc hwc : Measure ℝ) := by
  change ((reserveMarkIntensity η w a).restrict (Ioi b)).restrict (Ioi c) =
    (reserveMarkIntensity η w a).restrict (Ioi c)
  rw [Measure.restrict_restrict measurableSet_Ioi,inter_eq_left.mpr (Ioi_subset_Ioi hbc)]

end ProphetSecretary.Limiting
