import ProphetSecretary.Limiting.CountableCapBounds
import ProphetSecretary.Limiting.CountableMaximumDistribution
import ProphetSecretary.Probability.BoundedCDFMean

/-!
# The prophet benchmark of the actual capped countable model

Below the positive cap, the actual individual CDFs and Poisson upper tails
are unchanged. The full maximum CDF and bounded layer cake therefore identify
the capped benchmark with E[min(maximum,K)]. This is a distributional benchmark
identity and makes no assertion about convergence of policies.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Classical
namespace ProphetSecretary.Limiting.CountableInstance

lemma capAt_individual_probability_Iic (B : CountableInstance) (hZero : B.terminal=0)
    (K : ℝ≥0) (hK : 0<K) (i : ℕ) {t : ℝ} (ht : t<(K:ℝ)) :
    ((B.capAt hZero K hK).individuals i : Measure ℝ) (Iic t)=(B.individuals i : Measure ℝ) (Iic t) := by
  change ((B.individuals i : Measure ℝ).map (Model.capValue K)) (Iic t)=_
  rw [Measure.map_apply (Model.measurable_capValue K) measurableSet_Iic]
  congr 1
  ext x
  simp only [Set.mem_preimage,Set.mem_Iic,Model.capValue,min_le_iff,not_le.mpr ht,or_false]

lemma capAt_maximum_probability_Iic (B : CountableInstance) (hZero : B.terminal=0)
    (K : ℝ≥0) (hK : 0<K) {t : ℝ} (ht0 : 0<t) (htK : t<(K:ℝ)) :
    (B.capAt hZero K hK).valueLaw {v | (B.capAt hZero K hK).maximum v≤t}=B.valueLaw {v | B.maximum v≤t} := by
  let Q := B.capAt hZero K hK
  have hOld : (B.terminal:ℝ)<t := by simpa only [hZero,NNReal.coe_zero] using ht0
  have hNew : (Q.terminal:ℝ)<t := ht0
  rw [Q.maximum_probability_Iic hNew,B.maximum_probability_Iic hOld]
  have hIntensity : Q.intensity.real (Ioi t)=B.intensity.real (Ioi t) :=
    congrArg ENNReal.toReal (B.capAt_intensity_tail hZero K hK htK)
  rw [hIntensity]
  have hEach (i : ℕ) : (Q.individuals i : Measure ℝ) (Iic t)=(B.individuals i : Measure ℝ) (Iic t) :=
    B.capAt_individual_probability_Iic hZero K hK i htK
  simp_rw [hEach]

lemma capAt_expectedMaximum_eq_integral_min (B : CountableInstance) (hZero : B.terminal=0)
    (K : ℝ≥0) (hK : 0<K) :
    (B.capAt hZero K hK).expectedMaximum=∫ v, min (B.maximum v) (K:ℝ) ∂B.valueLaw := by
  let Q := B.capAt hZero K hK
  have hQRange : ∀ᵐ v ∂Q.valueLaw, Q.maximum v∈Icc (0:ℝ) K := by
    filter_upwards [Q.maximum_bounded,B.capAt_maximum_le hZero K hK] with v hv hKv
    exact ⟨hv.1,hKv⟩
  have hMinMeas : Measurable (fun v => min (B.maximum v) (K:ℝ)) := B.measurable_maximum.min measurable_const
  have hMinRange : ∀ᵐ v ∂B.valueLaw, min (B.maximum v) (K:ℝ)∈Icc (0:ℝ) K := by
    filter_upwards [B.maximum_bounded] with v hv
    have hv0 : 0≤B.maximum v := B.terminal.property.trans hv.1
    exact ⟨le_min hv0 K.property,min_le_right _ _⟩
  have hCDF : ∀ᵐ t ∂volume.restrict (Ioc (0:ℝ) K),
      Tendsto (fun _ : ℕ => Q.valueLaw.real {v | Q.maximum v≤t}) atTop
        (𝓝 (B.valueLaw.real {v | min (B.maximum v) (K:ℝ)≤t})) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (K:ℝ))] with t ht hne
    have htK : t<(K:ℝ) := lt_of_le_of_ne ht.2 hne
    have hEq : {v : ValueWorld | min (B.maximum v) (K:ℝ)≤t}={v | B.maximum v≤t} := by
      ext v
      simp only [Set.mem_setOf_eq,min_le_iff,not_le.mpr htK,or_false]
    have h : Q.valueLaw.real {v | Q.maximum v≤t}=B.valueLaw.real {v | B.maximum v≤t} :=
      congrArg ENNReal.toReal (B.capAt_maximum_probability_Iic hZero K hK ht.1 htK)
    rw [hEq,←h]
    exact tendsto_const_nhds
  have hLim := ProphetSecretary.Probability.tendsto_integrals_of_bounded_cdf
    (μ:=fun _ : ℕ => Q.valueLaw) (ν:=B.valueLaw) (X:=fun _ => Q.maximum)
    (Y:=fun v => min (B.maximum v) (K:ℝ)) (fun _ => Q.measurable_maximum) hMinMeas K
    (fun _ => hQRange) hMinRange hCDF
  exact tendsto_nhds_unique (tendsto_const_nhds : Tendsto (fun _ : ℕ => Q.expectedMaximum) atTop (𝓝 Q.expectedMaximum)) hLim

lemma maximum_cap_excess_integrable (B : CountableInstance) (K : ℝ≥0) :
    Integrable (fun v => Model.tailValue K (B.maximum v)) B.valueLaw := by
  apply B.integrable_maximum.abs.mono' ((Model.measurable_tailValue K).comp B.measurable_maximum).aestronglyMeasurable
  exact Eventually.of_forall fun v => by
    change ‖Model.tailValue K (B.maximum v)‖≤|B.maximum v|
    rw [Real.norm_eq_abs,abs_of_nonneg (Model.tailValue_nonnegative K _)]
    exact Model.tailValue_le_abs K _

lemma expectedMaximum_eq_cap_add_expectedExcess (B : CountableInstance) (hZero : B.terminal=0)
    (K : ℝ≥0) (hK : 0<K) :
    B.expectedMaximum=(B.capAt hZero K hK).expectedMaximum+
      ∫ v, Model.tailValue K (B.maximum v) ∂B.valueLaw := by
  have hMinInt : Integrable (fun v => min (B.maximum v) (K:ℝ)) B.valueLaw := by
    apply Integrable.of_bound (B.measurable_maximum.min measurable_const).aestronglyMeasurable (K:ℝ)
    filter_upwards [B.maximum_bounded] with v hv
    have hNonneg : 0≤min (B.maximum v) (K:ℝ) := le_min (B.terminal.property.trans hv.1) K.property
    rw [Real.norm_eq_abs,abs_of_nonneg hNonneg]
    exact min_le_right _ _
  rw [B.capAt_expectedMaximum_eq_integral_min hZero K hK,
    ←integral_add (f:=fun v => min (B.maximum v) (K:ℝ))
      (g:=fun v => Model.tailValue K (B.maximum v)) hMinInt (B.maximum_cap_excess_integrable K)]
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    change B.maximum v=min (B.maximum v) (K:ℝ)+Model.tailValue K (B.maximum v)
    have h := Model.sub_capValue_eq_tailValue K (B.maximum v)
    change B.maximum v-min (B.maximum v) (K:ℝ)=Model.tailValue K (B.maximum v) at h
    linarith only [h]

end ProphetSecretary.Limiting.CountableInstance
