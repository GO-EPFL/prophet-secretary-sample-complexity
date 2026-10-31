import ProphetSecretary.Limiting.HybridDeletion
import ProphetSecretary.Limiting.DurationKernel

/-!
# Poisson compensator with retained individual observations

The rule can stop at retained individual offers or anonymous Poisson offers. Each
retained zero arrival still reveals its identity. Deleting one anonymous candidate
preserves all these observations, and the constructed Mecke identity yields its
reached-band compensator with no count observation or future individual input.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def HybridRule.reachedPoissonBandCount (π : HybridRule n Seed) (B : Set ℝ)
    (v : HybridWorld n Seed) : ℝ≥0∞ :=
  ∑ j : Fin v.1.1, if (v.1.2 j).2 ∈ B ∧ π.ReachesPoisson v.2.2.2 v.2.1 v.2.2.1 v.1 j then 1 else 0

lemma HybridRule.measurable_reachedPoissonBandCount (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    {B : Set ℝ} (hB : MeasurableSet B) : Measurable (π.reachedPoissonBandCount B) := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × ProphetSecretary.Model.World n Seed
  have hr : Measurable (fun v : Ω => v.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hx (i : Fin n) : Measurable (fun v : Ω => v.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hu (i : Fin n) : Measurable (fun v : Ω => v.2.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hv (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  change Measurable (fun v : Ω => ∑ j : Fin N, if (v.1 j).2 ∈ B ∧
    (π.asFinitePolicy N).Reaches v.2.2.2 (combinedValues v.2.1 v.1) (combinedClocks v.2.2.1 v.1) (j.natAdd n)
      then (1 : ℝ≥0∞) else 0)
  apply Finset.measurable_fun_sum
  intro j _
  have hband : MeasurableSet {v : Ω | (v.1 j).2 ∈ B} := hB.preimage (measurable_snd.comp (hv j))
  have hreach := (π.asFinitePolicy N).measurableSet_reaches (π.asFinitePolicy_isMeasurable hπ N) hr
    (fun k => measurable_combinedValues_family _ hx _ hv k)
    (fun k => measurable_combinedClocks_family _ hu _ hv k) (j.natAdd n)
  exact Measurable.ite (hband.inter hreach) measurable_const measurable_const

omit [MeasurableSpace Seed] in
lemma HybridRule.reachedPoissonBandCount_le_count (π : HybridRule n Seed) (B : Set ℝ)
    (v : HybridWorld n Seed) : π.reachedPoissonBandCount B v ≤ (v.1.1 : ℝ≥0∞) := by
  unfold HybridRule.reachedPoissonBandCount
  calc
    _ ≤ ∑ _j : Fin v.1.1, (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> simp
    _ = _ := by simp

omit [MeasurableSpace Seed] in
lemma HybridRule.reachedPoissonBandCount_lt_top (π : HybridRule n Seed) (B : Set ℝ)
    (v : HybridWorld n Seed) : π.reachedPoissonBandCount B v < ∞ :=
  (π.reachedPoissonBandCount_le_count B v).trans_lt (by simp)

lemma HybridRule.mecke_durationKernel_ae (π : HybridRule n Seed)
    (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (B : Set ℝ) :
    meckeSum (durationKernel π.realizedDuration B) =ᵐ[hybridWorldLaw P μ ν] π.reachedPoissonBandCount B := by
  have hc := (Measure.quasiMeasurePreserving_fst (μ := configurationLaw μ) (ν := P.worldLaw ν)).ae
    (configuration_times_mem_Ioo μ)
  filter_upwards [hc] with v hv
  unfold meckeSum HybridRule.reachedPoissonBandCount
  apply Finset.sum_congr rfl
  intro j _
  have he := π.reachesPoisson_iff_le_deleted v.2.2.2 v.2.1 v.2.2.1 v.1 j (hv j).2.le
  change (if (v.1.2 j).2 ∈ B ∧ (v.1.2 j).1 ≤ π.stoppingTime v.2.2.2 v.2.1 v.2.2.1 (erasePoint v.1 j)
    then (1 : ℝ≥0∞) else 0) = _
  exact ite_congr (propext (and_congr_right (fun _ => he.symm))) (fun _ => rfl) (fun _ => rfl)

/-- Expected reached anonymous points equal band intensity times duration even
when stopping may occur at retained individual offers, including their zero arrivals. -/
lemma HybridRule.poisson_compensator (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {B : Set ℝ} (hB : MeasurableSet B) :
    (∫⁻ v, π.reachedPoissonBandCount B v ∂hybridWorldLaw P μ ν) =
      (μ : Measure ℝ) B * ENNReal.ofReal (π.meanDuration P μ ν) := by
  calc
    _ = ∫⁻ v, meckeSum (durationKernel π.realizedDuration B) v ∂hybridWorldLaw P μ ν :=
      (lintegral_congr_ae (π.mecke_durationKernel_ae P μ ν B)).symm
    _ = _ := mecke_durationKernel μ (P.worldLaw ν) π.realizedDuration (π.measurable_realizedDuration hπ)
      (π.realizedDuration_mem_unitInterval P μ ν) hB

lemma HybridRule.integrable_reachedPoissonBandCount (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {B : Set ℝ} (hB : MeasurableSet B) :
    Integrable (fun v => (π.reachedPoissonBandCount B v).toReal) (hybridWorldLaw P μ ν) := by
  apply integrable_toReal_of_lintegral_ne_top (π.measurable_reachedPoissonBandCount hπ hB).aemeasurable
  rw [π.poisson_compensator hπ P μ ν hB]
  exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top

lemma HybridRule.poisson_compensator_real (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {B : Set ℝ} (hB : MeasurableSet B) :
    (∫ v, (π.reachedPoissonBandCount B v).toReal ∂hybridWorldLaw P μ ν) =
      (μ : Measure ℝ).real B * π.meanDuration P μ ν := by
  rw [integral_toReal (π.measurable_reachedPoissonBandCount hπ hB).aemeasurable
    (Filter.Eventually.of_forall (π.reachedPoissonBandCount_lt_top B)), π.poisson_compensator hπ P μ ν hB,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (π.meanDuration_nonnegative P μ ν)]
  rfl

lemma HybridRule.poisson_compensator_scaled_intensity (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : ProphetSecretary.Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (u : ℝ≥0)
    {B : Set ℝ} (hB : MeasurableSet B) :
    (∫ v, (π.reachedPoissonBandCount B v).toReal ∂hybridWorldLaw P (u • μ) ν) =
      (u : ℝ) * (μ : Measure ℝ).real B * π.meanDuration P (u • μ) ν := by
  rw [π.poisson_compensator_real hπ P (u • μ) ν hB]
  change (((u : ℝ≥0∞) * (μ : Measure ℝ) B).toReal) * π.meanDuration P (u • μ) ν = _
  rw [ENNReal.toReal_mul]
  rfl

end ProphetSecretary.Limiting
