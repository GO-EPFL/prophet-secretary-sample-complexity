import ProphetSecretary.Limiting.ExtractedWeightedResidual

/-!
# A locally finite positive-mark intensity from a finite weighted measure

The reciprocal-value density erases every nonpositive mark, including a
possible artifact atom at zero of the weighted weak limit. The resulting
intensity need not have finite total mass near zero, but its mass above each
positive cutoff b is at most the weighted total mass divided by b.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Limiting

noncomputable def positiveReciprocalWeight (x : ℝ) : ENNReal :=
  if 0 < x then ENNReal.ofReal (1 / x) else 0

lemma measurable_positiveReciprocalWeight : Measurable positiveReciprocalWeight :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (measurable_const.div measurable_id).ennreal_ofReal measurable_const

noncomputable def positiveMarkIntensity (η : FiniteMeasure ℝ) : Measure ℝ :=
  (η : Measure ℝ).withDensity positiveReciprocalWeight

instance positiveMarkIntensity_sigmaFinite (η : FiniteMeasure ℝ) : SigmaFinite (positiveMarkIntensity η) := by
  apply SigmaFinite.withDensity_of_ne_top'
  intro x
  unfold positiveReciprocalWeight
  split_ifs <;> simp

lemma positiveMarkIntensity_nonpositive_zero (η : FiniteMeasure ℝ) :
    positiveMarkIntensity η (Iic (0 : ℝ)) = 0 := by
  rw [positiveMarkIntensity,withDensity_apply _ measurableSet_Iic]
  calc
    _ = ∫⁻ _x in Iic (0 : ℝ), (0 : ENNReal) ∂(η : Measure ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      exact if_neg (not_lt.mpr hx)
    _ = 0 := by simp

lemma positiveMarkIntensity_supported_interval (η : FiniteMeasure ℝ) {H : ℝ}
    (hcap : (η : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) :
    positiveMarkIntensity η (Ioc (0 : ℝ) H)ᶜ = 0 := by
  have hbase : positiveMarkIntensity η (Icc (0 : ℝ) H)ᶜ = 0 :=
    (withDensity_absolutelyContinuous _ _) hcap
  have hzero : positiveMarkIntensity η ((Icc (0 : ℝ) H)ᶜ ∪ Iic 0) = 0 :=
    measure_union_null hbase (positiveMarkIntensity_nonpositive_zero η)
  apply measure_mono_null _ hzero
  intro x hx
  by_cases hpos : 0 < x
  · exact Or.inl (fun hmem => hx ⟨hpos,hmem.2⟩)
  · exact Or.inr (not_lt.mp hpos)

/-- Local finiteness and its explicit cutoff dependence, before introducing
any Poisson process with this intensity. -/
theorem positiveMarkIntensity_tail_le (η : FiniteMeasure ℝ) {b : ℝ} (hb : 0 < b) :
    positiveMarkIntensity η (Ioi b) ≤ ENNReal.ofReal ((η.mass : ℝ) / b) := by
  rw [positiveMarkIntensity,withDensity_apply _ measurableSet_Ioi]
  have hbound : ∀ᵐ x ∂(η : Measure ℝ).restrict (Ioi b),
      positiveReciprocalWeight x ≤ ENNReal.ofReal (1 / b) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [positiveReciprocalWeight,if_pos (hb.trans hx)]
    exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le hb hx.le)
  calc
    _ ≤ ∫⁻ _x in Ioi b, ENNReal.ofReal (1/b) ∂(η : Measure ℝ) := lintegral_mono_ae hbound
    _ = ENNReal.ofReal (1/b) * (η : Measure ℝ) (Ioi b) := by simp
    _ ≤ ENNReal.ofReal (1/b) * (η : Measure ℝ) Set.univ :=
      mul_le_mul_of_nonneg_left (measure_mono (subset_univ _)) bot_le
    _ = ENNReal.ofReal ((η.mass : ℝ) / b) := by
      rw [← FiniteMeasure.ennreal_mass,← ENNReal.ofReal_coe_nnreal,← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / b)]
      congr 1
      ring

lemma positiveMarkIntensity_tail_lt_top (η : FiniteMeasure ℝ) {b : ℝ} (hb : 0 < b) :
    positiveMarkIntensity η (Ioi b) < ⊤ :=
  (positiveMarkIntensity_tail_le η hb).trans_lt ENNReal.ofReal_lt_top

/-- Every positive cutoff gives a genuine finite intensity measure. -/
noncomputable def positiveMarkIntensityAbove (η : FiniteMeasure ℝ) (b : ℝ) (hb : 0 < b) : FiniteMeasure ℝ :=
  ⟨(positiveMarkIntensity η).restrict (Ioi b),⟨by simpa using positiveMarkIntensity_tail_lt_top η hb⟩⟩

/-- Restricting a larger positive band to a smaller one preserves the same
constructed intensity; cutoff compatibility is an actual measure identity. -/
lemma positiveMarkIntensityAbove_restrict (η : FiniteMeasure ℝ) {b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hbc : b ≤ c) :
    ((positiveMarkIntensityAbove η b hb : Measure ℝ).restrict (Ioi c)) =
      (positiveMarkIntensityAbove η c hc : Measure ℝ) := by
  change ((positiveMarkIntensity η).restrict (Ioi b)).restrict (Ioi c) =
    (positiveMarkIntensity η).restrict (Ioi c)
  rw [Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi c ∩ Ioi b = Ioi c := inter_eq_left.mpr (Ioi_subset_Ioi hbc)
  rw [hset]

end ProphetSecretary.Limiting
