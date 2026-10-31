import ProphetSecretary.Limiting.CountableCapping
import ProphetSecretary.Limiting.CountableBenchmark

/-!
# The actual bound on capped marks

The original ambient cap is retained for the band representation. Nevertheless
all individual and anonymous marks of the capped model are at most K, so its
prophet benchmark is at most K as well.
-/

open MeasureTheory Set Filter
open scoped NNReal Classical
namespace ProphetSecretary.Limiting.CountableInstance

lemma capAt_individual_bounded (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K) (i : ℕ) :
    ∀ᵐ x ∂((B.capAt hZero K hK).individuals i : Measure ℝ), x≤(K:ℝ) := by
  change ∀ᵐ x ∂((B.individuals i : Measure ℝ).map (Model.capValue K)), x≤(K:ℝ)
  apply (ae_map_iff (Model.measurable_capValue K).aemeasurable measurableSet_Iic).mpr
  exact Eventually.of_forall fun _ => min_le_right _ _

lemma capAt_intensity_bounded (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K) :
    ∀ᵐ x ∂(B.capAt hZero K hK).intensity, x≤(K:ℝ) := by
  change ∀ᵐ x ∂B.intensity.map (Model.capValue K), x≤(K:ℝ)
  apply (ae_map_iff (Model.measurable_capValue K).aemeasurable measurableSet_Iic).mpr
  exact Eventually.of_forall fun _ => min_le_right _ _

lemma capAt_bandConfigurations_bounded (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K) :
    ∀ᵐ ω ∂(B.capAt hZero K hK).bandConfigurationsLaw, ∀ k j, ((ω k).2 j).2≤(K:ℝ) := by
  let Q := B.capAt hZero K hK
  apply ae_all_iff.mpr
  intro k
  have hSupp : ∀ᵐ x ∂(Q.bandIntensity k : Measure ℝ), x∈Ioc (0:ℝ) K := by
    filter_upwards [ae_restrict_of_ae Q.intensity_supported,
      ae_restrict_of_ae (B.capAt_intensity_bounded hZero K hK)] with x hx hKx
    exact ⟨hx.1,hKx⟩
  exact ((Q.bandConfiguration_measurePreserving k).quasiMeasurePreserving.ae
    (configuration_points_mem_band (Q.bandIntensity k) K hSupp)).mono fun _ hω j => (hω j).2.2

lemma capAt_maximum_le (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K) :
    ∀ᵐ v ∂(B.capAt hZero K hK).valueLaw, (B.capAt hZero K hK).maximum v≤(K:ℝ) := by
  let Q := B.capAt hZero K hK
  have hInd : ∀ᵐ x ∂Q.individualValuesLaw, ∀ i, x i≤(K:ℝ) := by
    apply ae_all_iff.mpr
    intro i
    exact (Q.individualValue_measurePreserving i).quasiMeasurePreserving.ae (B.capAt_individual_bounded hZero K hK i)
  have hX := (Measure.quasiMeasurePreserving_snd (μ:=Q.bandConfigurationsLaw) (ν:=Q.individualValuesLaw)).ae hInd
  have hCloud := (Measure.quasiMeasurePreserving_fst (μ:=Q.bandConfigurationsLaw) (ν:=Q.individualValuesLaw)).ae
    (B.capAt_bandConfigurations_bounded hZero K hK)
  filter_upwards [hX,hCloud] with v hx hp
  apply countableMaximum_le (by change (0:ℝ)≤K;exact K.property) K.property
  intro k
  exact max_le (hx k) (Model.Instance.maximum_le _ K.property (fun j => hp k j))

lemma capAt_expectedMaximum_le (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K) :
    (B.capAt hZero K hK).expectedMaximum≤(K:ℝ) := by
  have h := integral_mono_ae (B.capAt hZero K hK).integrable_maximum (integrable_const (K:ℝ)) (B.capAt_maximum_le hZero K hK)
  simpa only [expectedMaximum,integral_const,probReal_univ,one_smul] using h

end ProphetSecretary.Limiting.CountableInstance
