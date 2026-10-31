import ProphetSecretary.Limiting.OmissionPolicy

/-!
# The actual omitted-cloud seed has the required locally finite past

Support and finite mass of every construction band are derived from the
constructed low-cloud law. Its total intensity may be infinite. Consequently
the simulator's measurable bandwise past is the exact strict past almost surely.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def LowCloudRegular (B : CountableInstance) (b : ℝ) (μ : Measure Point) : Prop :=
  μ (univ ×ˢ Ioc (B.terminal : ℝ) b)ᶜ = 0 ∧
    ∀ k, μ (univ ×ˢ B.markBand k) < ⊤

lemma measurableSet_lowCloudRegular (B : CountableInstance) (b : ℝ) :
    MeasurableSet {μ : Measure Point | LowCloudRegular B b μ} := by
  unfold LowCloudRegular
  simp only [setOf_and,setOf_forall]
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun
      (Measure.measurable_coe (MeasurableSet.univ.prod measurableSet_Ioc).compl) measurable_const
  · exact MeasurableSet.iInter (fun k => measurableSet_lt
      (Measure.measurable_coe (MeasurableSet.univ.prod (B.measurableSet_markBand k))) measurable_const)

lemma lowCloudLaw_regular_ae (B : CountableInstance) (b : ℝ) :
    ∀ᵐ μ ∂B.lowCloudLaw b, LowCloudRegular B b μ := by
  change ∀ᵐ μ ∂B.bandConfigurationsLaw.map
    (fun ω => (bandCountingMeasure ω).restrict (univ ×ˢ Ioc (B.terminal : ℝ) b)), LowCloudRegular B b μ
  rw [ae_map_iff (B.measurable_lowCloud b).aemeasurable (B.measurableSet_lowCloudRegular b)]
  have hband (k : ℕ) : ∀ᵐ ω ∂B.bandConfigurationsLaw,
      bandCountingMeasure ω (univ ×ˢ B.markBand k) < ⊤ :=
    B.bandCountingMeasure_region_finite_ae (B.terminal_lt_markCutoff k)
      (MeasurableSet.univ.prod (B.measurableSet_markBand k))
      (fun _ hp => ⟨hp.1,B.markBand_subset_tail k hp.2⟩)
  filter_upwards [ae_all_iff.mpr hband] with ω hω
  constructor
  · rw [Measure.restrict_apply (MeasurableSet.univ.prod measurableSet_Ioc).compl]
    simp only [compl_inter_self,measure_empty]
  · intro k
    rw [Measure.restrict_apply (MeasurableSet.univ.prod (B.measurableSet_markBand k))]
    exact (measure_mono inter_subset_left).trans_lt (hω k)

lemma LowCloudRegular.past_eq {B : CountableInstance} {b : ℝ} {μ : Measure Point}
    (h : LowCloudRegular B b μ) (t : ℝ) : omittedCloudPast B μ t = μ.restrict (Iio t ×ˢ univ) := by
  have hs : ∀ᵐ p ∂μ, p ∈ univ ×ˢ Ioc (B.terminal : ℝ) b := by
    have he := measure_eq_zero_iff_ae_notMem.mp h.1
    simpa only [mem_compl_iff,not_not] using he
  apply omittedCloudPast_eq B μ (hs.mono (fun _ hp => hp.2.1))
  intro k
  constructor
  simpa only [Measure.restrict_apply_univ] using h.2 k

lemma LowCloudRegular.marks_le {B : CountableInstance} {b : ℝ} {μ : Measure Point}
    (h : LowCloudRegular B b μ) : ∀ᵐ p ∂μ, p.2 ≤ b := by
  have he := measure_eq_zero_iff_ae_notMem.mp h.1
  filter_upwards [he] with p hp
  have hs : p ∈ univ ×ˢ Ioc (B.terminal : ℝ) b := by simpa only [mem_compl_iff,not_not] using hp
  exact hs.2.2

end ProphetSecretary.Limiting.CountableInstance
