import ProphetSecretary.Limiting.CountableInstance
import ProphetSecretary.Limiting.Support
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Independent finite bands for the countable marked configuration

Disjoint bands exhaust all marks above the reserve. Each carries the already
constructed finite Poisson configuration; the infinite product constructs their
independence. The generation band and array index remain analytical labels and
are not inputs to an online rule.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal Topology

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance)

noncomputable def markCutoff (k : ℕ) : ℝ :=
  (B.terminal : ℝ) + 1 / ((k : ℝ) + 1)

lemma terminal_lt_markCutoff (k : ℕ) : (B.terminal : ℝ) < B.markCutoff k := by
  unfold markCutoff
  have hp : 0 < 1 / ((k : ℝ) + 1) := by positivity
  linarith only [hp]

lemma markCutoff_tendsto : Tendsto B.markCutoff atTop (𝓝 (B.terminal : ℝ)) := by
  change Tendsto (fun k : ℕ => (B.terminal : ℝ) + 1 / ((k : ℝ) + 1)) atTop (𝓝 (B.terminal : ℝ))
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (B.terminal : ℝ)
  rw [add_zero] at h
  exact h

noncomputable def markBand (k : ℕ) : Set ℝ :=
  disjointed (fun j => Ioi (B.markCutoff j)) k

lemma measurableSet_markBand (k : ℕ) : MeasurableSet (B.markBand k) := by
  rw [markBand,disjointed_eq_inter_compl]
  exact measurableSet_Ioi.inter (MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => measurableSet_Ioi.compl)

lemma markBand_subset_tail (k : ℕ) : B.markBand k ⊆ Ioi (B.markCutoff k) :=
  disjointed_subset _ k

lemma markBands_disjoint : Pairwise (fun i j => Disjoint (B.markBand i) (B.markBand j)) :=
  disjoint_disjointed _

lemma iUnion_markBand : (⋃ k, B.markBand k) = Ioi (B.terminal : ℝ) := by
  change (⋃ k, disjointed (fun j => Ioi (B.markCutoff j)) k) = _
  rw [iUnion_disjointed]
  ext x
  simp only [mem_iUnion,mem_Ioi]
  constructor
  · rintro ⟨k,hk⟩
    exact (B.terminal_lt_markCutoff k).trans hk
  · intro hx
    have he : ∀ᶠ k in atTop, B.markCutoff k < x :=
      B.markCutoff_tendsto.eventually (gt_mem_nhds hx)
    exact he.exists

noncomputable def bandIntensity (k : ℕ) : FiniteMeasure ℝ :=
  ⟨B.intensity.restrict (B.markBand k), ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (B.markBand_subset_tail k)).trans_lt
      (B.intensity_tail_finite _ (B.terminal_lt_markCutoff k))⟩⟩

lemma sum_bandIntensity :
    Measure.sum (fun k => (B.bandIntensity k : Measure ℝ)) = B.intensity := by
  change Measure.sum (fun k => B.intensity.restrict (B.markBand k)) = B.intensity
  rw [← Measure.restrict_iUnion B.markBands_disjoint B.measurableSet_markBand,B.iUnion_markBand]
  exact Measure.restrict_eq_self_of_ae_mem (B.intensity_supported.mono fun _ hx => hx.1)

abbrev BandConfigurations := ℕ → Configuration

noncomputable def bandConfigurationsLaw : Measure BandConfigurations :=
  Measure.infinitePi (fun k => configurationLaw (B.bandIntensity k))

instance bandConfigurationsLaw_probability : IsProbabilityMeasure B.bandConfigurationsLaw := by
  unfold bandConfigurationsLaw
  infer_instance

lemma bandConfigurations_independent :
    iIndepFun (fun k (ω : BandConfigurations) => ω k) B.bandConfigurationsLaw :=
  iIndepFun_infinitePi (fun _ => measurable_id)

lemma bandConfiguration_measurePreserving (k : ℕ) :
    MeasurePreserving (fun ω : BandConfigurations => ω k) B.bandConfigurationsLaw
      (configurationLaw (B.bandIntensity k)) :=
  measurePreserving_eval_infinitePi _ k

lemma bandIntensity_supported (k : ℕ) :
    ∀ᵐ x ∂(B.bandIntensity k : Measure ℝ), x ∈ Ioc (0 : ℝ) B.cap := by
  filter_upwards [ae_restrict_of_ae B.intensity_supported] with x hx
  exact ⟨B.terminal.property.trans_lt hx.1,hx.2⟩

lemma bandConfigurations_supported :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, ∀ k j,
      ((ω k).2 j).1 ∈ Ioo (0 : ℝ) 1 ∧ ((ω k).2 j).2 ∈ Ioc (0 : ℝ) B.cap := by
  apply ae_all_iff.mpr
  intro k
  exact (B.bandConfiguration_measurePreserving k).quasiMeasurePreserving.ae
    (configuration_points_mem_band (B.bandIntensity k) B.cap (B.bandIntensity_supported k))

set_option maxHeartbeats 800000 in
lemma bandConfigurations_marks_in_band :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, ∀ k j, ((ω k).2 j).2 ∈ B.markBand k := by
  apply ae_all_iff.mpr
  intro k
  have hm : ∀ᵐ x ∂(B.bandIntensity k : Measure ℝ), x ∈ B.markBand k :=
    ae_restrict_mem (B.measurableSet_markBand k)
  have hpoint : ∀ᵐ p : Point ∂ProphetSecretary.Limiting.intensity (B.bandIntensity k), p.2 ∈ B.markBand k :=
    (Measure.quasiMeasurePreserving_snd (μ := Model.Instance.uniformClock)
      (ν := (B.bandIntensity k : Measure ℝ))).ae hm
  have hl : ∀ᵐ ω ∂configurationLaw (B.bandIntensity k), ∀ j, (ω.2 j).2 ∈ B.markBand k :=
    all_points_in_of_intensity_compl_null (B.bandIntensity k)
      ((B.measurableSet_markBand k).preimage measurable_snd) (ae_iff.mp hpoint)
  exact (B.bandConfiguration_measurePreserving k).quasiMeasurePreserving.ae hl

lemma eventually_bands_below {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    ∃ K : ℕ, ∀ k, K < k → ∀ x ∈ B.markBand k, x ≤ b := by
  obtain ⟨K,hK⟩ := (B.markCutoff_tendsto.eventually (gt_mem_nhds hb)).exists
  refine ⟨K,?_⟩
  intro k hk x hx
  rw [markBand,disjointed_eq_inter_compl] at hx
  have hn : x ∉ Ioi (B.markCutoff K) := mem_iInter.mp (mem_iInter.mp hx.2 K) hk
  exact (not_lt.mp hn).trans hK.le

/-- The observed positive band above any level b>a uses only finitely many
of the actual finite configurations, almost surely. -/
lemma ae_eventually_no_points_above {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, ∃ K : ℕ, ∀ k, K < k → ∀ j, ((ω k).2 j).2 ≤ b := by
  obtain ⟨K,hK⟩ := B.eventually_bands_below hb
  exact B.bandConfigurations_marks_in_band.mono (fun ω hω =>
    ⟨K,fun k hk j => hK k hk _ (hω k j)⟩)

end ProphetSecretary.Limiting.CountableInstance
