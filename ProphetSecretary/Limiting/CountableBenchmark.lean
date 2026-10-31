import ProphetSecretary.Limiting.CountablePoissonBands
import ProphetSecretary.Limiting.CountableMaximum
import ProphetSecretary.Limiting.HybridOutcomes

/-!
# The realized maximum of the countable configuration

The benchmark is an actual random variable on the independent individual and
band-configuration product. Finite-prefix expectations converge by monotone
convergence. Cofinal cutoff truncations recover the same benchmark.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal Topology

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance)

abbrev ValueWorld := BandConfigurations × (ℕ → ℝ)

noncomputable def valueLaw : Measure ValueWorld :=
  B.bandConfigurationsLaw.prod B.individualValuesLaw

instance valueLaw_probability : IsProbabilityMeasure B.valueLaw := by
  unfold valueLaw
  infer_instance

noncomputable def bandMaximum (ω : Configuration) : ℝ :=
  Model.Instance.maximum (fun j : Fin ω.1 => (ω.2 j).2)

lemma measurable_bandMaximum : Measurable bandMaximum := by
  apply measurable_of_configuration_branches
  intro N
  exact Model.Instance.measurable_maximum.comp (measurable_pi_lambda _ (fun j =>
    measurable_snd.comp (measurable_pi_apply j)))

noncomputable def candidateMaxima (v : ValueWorld) (k : ℕ) : ℝ :=
  max (v.2 k) (bandMaximum (v.1 k))

lemma measurable_candidateMaxima (k : ℕ) : Measurable (fun v : ValueWorld => candidateMaxima v k) :=
  ((measurable_pi_apply k).comp measurable_snd).max
    (measurable_bandMaximum.comp ((measurable_pi_apply k).comp measurable_fst))

lemma candidateMaxima_bounded : ∀ᵐ v ∂B.valueLaw, ∀ k, candidateMaxima v k ≤ (B.cap : ℝ) := by
  have hx := (Measure.quasiMeasurePreserving_snd (μ := B.bandConfigurationsLaw)
    (ν := B.individualValuesLaw)).ae B.individual_values_supported
  have hp := (Measure.quasiMeasurePreserving_fst (μ := B.bandConfigurationsLaw)
    (ν := B.individualValuesLaw)).ae B.bandConfigurations_supported
  filter_upwards [hx,hp] with v hv hc
  intro k
  apply max_le (hv k).2
  exact Model.Instance.maximum_le _ B.cap.property (fun j => (hc k j).2.2)

noncomputable def maximumPrefix (N : ℕ) (v : ValueWorld) : ℝ :=
  prefixMaximum B.terminal (candidateMaxima v) N

noncomputable def maximum (v : ValueWorld) : ℝ :=
  countableMaximum B.terminal (candidateMaxima v)

lemma measurable_maximumPrefix (N : ℕ) : Measurable (B.maximumPrefix N) :=
  measurable_prefixMaximum _ measurable_candidateMaxima N

lemma measurable_maximum : Measurable B.maximum :=
  measurable_countableMaximum _ measurable_candidateMaxima

lemma maximum_bounded : ∀ᵐ v ∂B.valueLaw, B.maximum v ∈ Icc (B.terminal : ℝ) B.cap := by
  filter_upwards [B.candidateMaxima_bounded] with v hv
  exact ⟨terminal_le_countableMaximum (show (B.terminal : ℝ) ≤ B.cap by exact_mod_cast B.terminal_le_cap)
    B.cap.property _ hv,
    countableMaximum_le (show (B.terminal : ℝ) ≤ B.cap by exact_mod_cast B.terminal_le_cap) B.cap.property _ hv⟩

lemma integrable_maximum : Integrable B.maximum B.valueLaw := by
  apply Integrable.of_bound B.measurable_maximum.aestronglyMeasurable B.cap
  filter_upwards [B.maximum_bounded] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg (B.terminal.property.trans hv.1)]
  exact hv.2

noncomputable def expectedMaximum : ℝ := ∫ v, B.maximum v ∂B.valueLaw

lemma expectedMaximum_prefix_limit :
    Tendsto (fun N => ∫ v, B.maximumPrefix N v ∂B.valueLaw) atTop (𝓝 B.expectedMaximum) :=
  integral_prefixMaximum_tendsto B.valueLaw B.terminal.property
    (show (B.terminal : ℝ) ≤ B.cap by exact_mod_cast B.terminal_le_cap)
    B.cap.property measurable_candidateMaxima B.candidateMaxima_bounded

/-- Every individual value is included in the actual maximum, without deleting
its zero-valued observation from the execution model. -/
lemma individual_le_maximum : ∀ᵐ v ∂B.valueLaw, ∀ i, v.2 i ≤ B.maximum v := by
  filter_upwards [B.candidateMaxima_bounded] with v hv
  intro i
  exact (le_max_left _ _).trans (le_countableMaximum
    (show (B.terminal : ℝ) ≤ B.cap by exact_mod_cast B.terminal_le_cap) B.cap.property _ hv i)

lemma mark_le_maximum : ∀ᵐ v ∂B.valueLaw, ∀ k j, ((v.1 k).2 j).2 ≤ B.maximum v := by
  filter_upwards [B.candidateMaxima_bounded] with v hv
  intro k j
  have hm : ((v.1 k).2 j).2 ≤ bandMaximum (v.1 k) := by
    exact Model.Instance.le_maximum (fun i : Fin (v.1 k).1 => ((v.1 k).2 i).2) j
  exact hm.trans ((le_max_right _ _).trans (le_countableMaximum
    (show (B.terminal : ℝ) ≤ B.cap by exact_mod_cast B.terminal_le_cap) B.cap.property _ hv k))

end ProphetSecretary.Limiting.CountableInstance
