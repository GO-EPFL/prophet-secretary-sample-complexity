import ProphetSecretary.Limiting.AnonymousPolicy

/-!
# Reached-band compensator for anonymous Poisson policies

A reached point is tested against the stopping time of its actual deleted
execution. The constructed Palm identity and independent uniform time density
therefore give expected reached count equal to intensity times expected duration.
Every count uses the same anonymous rule, with no realized-count observation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def AnonymousRule.reachedBandCount (π : AnonymousRule Seed) (B : Set ℝ) (v : World Seed) : ℝ≥0∞ :=
  ∑ j : Fin v.1.1, if (v.1.2 j).2 ∈ B ∧ π.Reaches v.2 v.1 j then 1 else 0

lemma AnonymousRule.measurable_reachedBandCount (π : AnonymousRule Seed) (hπ : π.IsMeasurable)
    {B : Set ℝ} (hB : MeasurableSet B) : Measurable (π.reachedBandCount B) := by
  apply measurable_of_configuration_prod_branches
  intro N
  change Measurable (fun v : (Fin N → Point) × Seed => ∑ j : Fin N,
    if (v.1 j).2 ∈ B ∧ π.Reaches v.2 (configurationMk N v.1) j then (1 : ℝ≥0∞) else 0)
  apply Finset.measurable_fun_sum
  intro j _
  have hband : MeasurableSet {v : (Fin N → Point) × Seed | (v.1 j).2 ∈ B} :=
    hB.preimage (measurable_snd.comp ((measurable_pi_apply j).comp measurable_fst))
  have hreach : MeasurableSet {v : (Fin N → Point) × Seed | π.Reaches v.2 (configurationMk N v.1) j} :=
    (π.asFinitePolicy N).measurableSet_reaches (π.asFinitePolicy_isMeasurable hπ N) measurable_snd
    (fun k => measurable_snd.comp ((measurable_pi_apply k).comp measurable_fst))
    (fun k => measurable_fst.comp ((measurable_pi_apply k).comp measurable_fst)) j
  exact Measurable.ite (hband.inter hreach) measurable_const measurable_const

omit [MeasurableSpace Seed] in
lemma AnonymousRule.reachedBandCount_le_count (π : AnonymousRule Seed) (B : Set ℝ) (v : World Seed) :
    π.reachedBandCount B v ≤ (v.1.1 : ℝ≥0∞) := by
  unfold AnonymousRule.reachedBandCount
  calc
    _ ≤ ∑ _j : Fin v.1.1, (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> simp
    _ = _ := by simp

omit [MeasurableSpace Seed] in
lemma AnonymousRule.reachedBandCount_lt_top (π : AnonymousRule Seed) (B : Set ℝ) (v : World Seed) :
    π.reachedBandCount B v < ∞ :=
  (π.reachedBandCount_le_count B v).trans_lt (by simp)

noncomputable def AnonymousRule.reachKernel (π : AnonymousRule Seed) (B : Set ℝ) (q : Point × World Seed) : ℝ≥0∞ :=
  if q.1.2 ∈ B ∧ q.1.1 ≤ π.stoppingTime q.2.2 q.2.1 then 1 else 0

lemma AnonymousRule.measurable_reachKernel (π : AnonymousRule Seed) (hπ : π.IsMeasurable)
    {B : Set ℝ} (hB : MeasurableSet B) : Measurable (π.reachKernel B) := by
  have hband : MeasurableSet {q : Point × World Seed | q.1.2 ∈ B} :=
    hB.preimage (measurable_snd.comp measurable_fst)
  have htime : Measurable (fun q : Point × World Seed => q.1.1) := measurable_fst.comp measurable_fst
  have hstop : Measurable (fun q : Point × World Seed => π.stoppingTime q.2.2 q.2.1) :=
    (π.measurable_stoppingTime hπ).comp measurable_snd
  exact Measurable.ite (hband.inter (measurableSet_le htime hstop)) measurable_const measurable_const

lemma AnonymousRule.meckeSum_reachKernel_ae (π : AnonymousRule Seed)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (B : Set ℝ) :
    meckeSum (π.reachKernel B) =ᵐ[worldLaw μ ν] π.reachedBandCount B := by
  have hc := (Measure.quasiMeasurePreserving_fst (μ := configurationLaw μ) (ν := ν)).ae
    (configuration_times_mem_Ioo μ)
  filter_upwards [hc] with v hv
  unfold meckeSum AnonymousRule.reachedBandCount
  apply Finset.sum_congr rfl
  intro j _
  have he := π.reaches_iff_le_deleted v.2 v.1 j (hv j).2.le
  change (if (v.1.2 j).2 ∈ B ∧ (v.1.2 j).1 ≤ π.stoppingTime v.2 (erasePoint v.1 j) then (1 : ℝ≥0∞) else 0) = _
  exact ite_congr (propext (and_congr_right (fun _ => he.symm))) (fun _ => rfl) (fun _ => rfl)

lemma uniformClock_Iic {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ProphetSecretary.Model.Instance.uniformClock (Iic s) = ENNReal.ofReal s := by
  have he : Iic s ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) s := by
    ext t
    constructor
    · rintro ⟨hts, ht0, _ht1⟩
      exact ⟨ht0, hts⟩
    · rintro ⟨ht0, hts⟩
      exact ⟨hts, ht0, hts.trans hs.2⟩
  rw [ProphetSecretary.Model.Instance.uniformClock, Measure.restrict_apply measurableSet_Iic, he, Real.volume_Icc, sub_zero]

noncomputable def AnonymousRule.meanDuration (π : AnonymousRule Seed) (μ : FiniteMeasure ℝ) (ν : Measure Seed) : ℝ :=
  ∫ v, π.stoppingTime v.2 v.1 ∂worldLaw μ ν

lemma AnonymousRule.meanDuration_nonnegative (π : AnonymousRule Seed) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] : 0 ≤ π.meanDuration μ ν := by
  apply integral_nonneg_of_ae
  exact (π.stoppingTime_mem_unitInterval μ ν).mono (fun _ h => h.1)

/-- Actual reached-band compensator on the normalized unit horizon, including
independent policy randomness and all history-dependent anonymous decisions. -/
lemma AnonymousRule.compensator (π : AnonymousRule Seed) (hπ : π.IsMeasurable)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {B : Set ℝ} (hB : MeasurableSet B) :
    (∫⁻ v, π.reachedBandCount B v ∂worldLaw μ ν) =
      (μ : Measure ℝ) B * ENNReal.ofReal (π.meanDuration μ ν) := by
  have hF := π.measurable_reachKernel hπ hB
  have hinner : ∀ᵐ v ∂worldLaw μ ν,
      (∫⁻ p, π.reachKernel B (p, v) ∂intensity μ) =
        ENNReal.ofReal (π.stoppingTime v.2 v.1) * (μ : Measure ℝ) B := by
    filter_upwards [π.stoppingTime_mem_unitInterval μ ν] with v hv
    have he : (fun p : Point => π.reachKernel B (p, v)) =
        (Iic (π.stoppingTime v.2 v.1) ×ˢ B).indicator 1 := by
      funext p
      simp [AnonymousRule.reachKernel, Set.indicator_apply, and_comm]
    rw [he, lintegral_indicator_one (measurableSet_Iic.prod hB), intensity, Measure.prod_prod, uniformClock_Iic hv]
  have hof := ofReal_integral_eq_lintegral_ofReal (π.integrable_stoppingTime hπ μ ν)
    ((π.stoppingTime_mem_unitInterval μ ν).mono (fun _ h => h.1))
  calc
    _ = ∫⁻ v, meckeSum (π.reachKernel B) v ∂worldLaw μ ν :=
      (lintegral_congr_ae (π.meckeSum_reachKernel_ae μ ν B)).symm
    _ = ∫⁻ q, π.reachKernel B q ∂(intensity μ).prod (worldLaw μ ν) := mecke μ ν _ hF
    _ = ∫⁻ v, ∫⁻ p, π.reachKernel B (p, v) ∂intensity μ ∂worldLaw μ ν := lintegral_prod_symm _ hF.aemeasurable
    _ = ∫⁻ v, ENNReal.ofReal (π.stoppingTime v.2 v.1) * (μ : Measure ℝ) B ∂worldLaw μ ν := lintegral_congr_ae hinner
    _ = (∫⁻ v, ENNReal.ofReal (π.stoppingTime v.2 v.1) ∂worldLaw μ ν) * (μ : Measure ℝ) B :=
      lintegral_mul_const _ (π.measurable_stoppingTime hπ).ennreal_ofReal
    _ = _ := by rw [← hof]; exact mul_comm _ _

lemma AnonymousRule.integrable_reachedBandCount (π : AnonymousRule Seed) (hπ : π.IsMeasurable)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {B : Set ℝ} (hB : MeasurableSet B) :
    Integrable (fun v => (π.reachedBandCount B v).toReal) (worldLaw μ ν) := by
  apply integrable_toReal_of_lintegral_ne_top (π.measurable_reachedBandCount hπ hB).aemeasurable
  rw [π.compensator hπ μ ν hB]
  exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top

lemma AnonymousRule.compensator_real (π : AnonymousRule Seed) (hπ : π.IsMeasurable)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {B : Set ℝ} (hB : MeasurableSet B) :
    (∫ v, (π.reachedBandCount B v).toReal ∂worldLaw μ ν) = (μ : Measure ℝ).real B * π.meanDuration μ ν := by
  rw [integral_toReal (π.measurable_reachedBandCount hπ hB).aemeasurable
    (Filter.Eventually.of_forall (π.reachedBandCount_lt_top B)), π.compensator hπ μ ν hB,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (π.meanDuration_nonnegative μ ν)]
  rfl

/-- Under remaining-horizon rescaling the normalized process has intensity `uμ`;
its reached-band expectation has the explicit physical-horizon factor `u`. -/
lemma AnonymousRule.compensator_scaled_intensity (π : AnonymousRule Seed) (hπ : π.IsMeasurable)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (u : ℝ≥0)
    {B : Set ℝ} (hB : MeasurableSet B) :
    (∫ v, (π.reachedBandCount B v).toReal ∂worldLaw (u • μ) ν) =
      (u : ℝ) * (μ : Measure ℝ).real B * π.meanDuration (u • μ) ν := by
  rw [π.compensator_real hπ (u • μ) ν hB]
  change (((u : ℝ≥0∞) * (μ : Measure ℝ) B).toReal) * π.meanDuration (u • μ) ν = _
  rw [ENNReal.toReal_mul]
  rfl

end ProphetSecretary.Limiting
