import ProphetSecretary.Limiting.Campbell
import ProphetSecretary.Model.Independence

/-!
# Support and arrival regularity of finite marked configurations

A finite mark intensity supported on `(0,H]` produces only such marks, including
when the intensity is zero. Actual arrival times lie strictly between the endpoints
and are pairwise distinct almost surely. These facts are derived from the constructed
law, rather than imposed on a policy or a random configuration interface.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

lemma ae_configuration_of_fibers (μ : FiniteMeasure ℝ) (p : Configuration → Prop)
    (hp : MeasurableSet {ω | p ω})
    (hf : ∀ N, ∀ᵐ v : Fin N → Point ∂arrayLaw μ N, p (configurationMk N v)) :
    ∀ᵐ ω ∂configurationLaw μ, p ω := by
  rw [configurationLaw, Measure.ae_sum_iff]
  intro N
  have h : ∀ᵐ ω ∂fiberLaw μ N, p ω := by
    rw [fiberLaw, ae_map_iff (measurable_configuration_mk N).aemeasurable hp]
    exact hf N
  exact Measure.ae_smul_measure h _

lemma all_points_in_of_intensity_compl_null (μ : FiniteMeasure ℝ) {S : Set Point}
    (hS : MeasurableSet S) (hnull : intensity μ Sᶜ = 0) :
    ∀ᵐ ω ∂configurationLaw μ, ∀ j : Fin ω.1, ω.2 j ∈ S := by
  have he := expected_count μ hS.compl
  rw [hnull] at he
  have hm := (Measure.measurable_coe hS.compl).comp measurable_countingMeasure
  have hz := (lintegral_eq_zero_iff hm).mp he
  filter_upwards [hz] with ω hω
  change countingMeasure ω Sᶜ = 0 at hω
  simp only [countingMeasure, Measure.coe_finsetSum, Finset.sum_apply] at hω
  intro j
  by_contra hj
  have hmem : ω.2 j ∈ Sᶜ := hj
  have hsingle : (Measure.dirac (ω.2 j)) Sᶜ ≤ ∑ k : Fin ω.1, (Measure.dirac (ω.2 k)) Sᶜ :=
    Finset.single_le_sum (f := fun k : Fin ω.1 => (Measure.dirac (ω.2 k)) Sᶜ)
      (fun _ _ => zero_le) (Finset.mem_univ j)
  rw [hω] at hsingle
  simp [Measure.dirac_apply' _ hS.compl, Set.indicator, hmem] at hsingle

lemma uniformClock_mem_Ioo :
    ∀ᵐ t : ℝ ∂ProphetSecretary.Model.Instance.uniformClock, t ∈ Ioo (0 : ℝ) 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Icc, ProphetSecretary.Model.Instance.uniformClock.ae_ne 0,
    ProphetSecretary.Model.Instance.uniformClock.ae_ne 1] with t ht h0 h1
  exact ⟨lt_of_le_of_ne ht.1 h0.symm, lt_of_le_of_ne ht.2 h1⟩

lemma configuration_times_mem_Ioo (μ : FiniteMeasure ℝ) :
    ∀ᵐ ω ∂configurationLaw μ, ∀ j : Fin ω.1, (ω.2 j).1 ∈ Ioo (0 : ℝ) 1 := by
  have ht : ∀ᵐ p : Point ∂intensity μ, p.1 ∈ Ioo (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst (μ := ProphetSecretary.Model.Instance.uniformClock) (ν := (μ : Measure ℝ))).ae
      uniformClock_mem_Ioo
  exact all_points_in_of_intensity_compl_null μ (S := {p : Point | p.1 ∈ Ioo (0 : ℝ) 1})
    (measurableSet_Ioo.preimage measurable_fst) (ae_iff.mp ht)

/-- The construction realizes a finite band intensity on `(0,H]` as actual
nonnegative bounded offers, with no positivity assumption on total intensity. -/
lemma configuration_points_mem_band (μ : FiniteMeasure ℝ) (H : ℝ)
    (hμ : ∀ᵐ x : ℝ ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) :
    ∀ᵐ ω ∂configurationLaw μ, ∀ j : Fin ω.1,
      (ω.2 j).1 ∈ Ioo (0 : ℝ) 1 ∧ (ω.2 j).2 ∈ Ioc (0 : ℝ) H := by
  have ht : ∀ᵐ p : Point ∂intensity μ, p.1 ∈ Ioo (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst (μ := ProphetSecretary.Model.Instance.uniformClock) (ν := (μ : Measure ℝ))).ae
      uniformClock_mem_Ioo
  have hx : ∀ᵐ p : Point ∂intensity μ, p.2 ∈ Ioc (0 : ℝ) H :=
    (Measure.quasiMeasurePreserving_snd (μ := ProphetSecretary.Model.Instance.uniformClock) (ν := (μ : Measure ℝ))).ae hμ
  have hp : ∀ᵐ p : Point ∂intensity μ, p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) H := by
    filter_upwards [ht, hx] with p hpt hpx
    exact ⟨hpt, hpx⟩
  exact all_points_in_of_intensity_compl_null μ (measurableSet_Ioo.prod measurableSet_Ioc) (ae_iff.mp hp)

lemma array_times_measurePreserving (μ : FiniteMeasure ℝ) (N : ℕ) :
    MeasurePreserving (fun v : Fin N → Point => fun j => (v j).1) (arrayLaw μ N)
      (ProphetSecretary.Model.Instance.clocksLaw N) := by
  have hpair := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N)
    (fun _ => ProphetSecretary.Model.Instance.uniformClock) (fun _ => (μ.normalize : Measure ℝ))
  exact measurePreserving_fst.comp hpair

lemma measurableSet_configuration_times_injective :
    MeasurableSet {ω : Configuration | Function.Injective (fun j : Fin ω.1 => (ω.2 j).1)} := by
  apply measurableSet_setOf.mpr
  apply measurable_of_configuration_branches
  intro N
  apply measurableSet_setOf.mp
  change MeasurableSet {v : Fin N → Point | ∀ j k, (v j).1 = (v k).1 → j = k}
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro k
  by_cases hjk : j = k
  · simp [hjk]
  · simpa only [hjk, imp_false, Set.compl_setOf, Function.comp_apply] using
      (measurableSet_eq_fun (measurable_fst.comp (measurable_pi_apply j))
        (measurable_fst.comp (measurable_pi_apply k))).compl

lemma configuration_times_distinct (μ : FiniteMeasure ℝ) :
    ∀ᵐ ω ∂configurationLaw μ, Function.Injective (fun j : Fin ω.1 => (ω.2 j).1) := by
  apply ae_configuration_of_fibers μ _ measurableSet_configuration_times_injective
  intro N
  exact (array_times_measurePreserving μ N).quasiMeasurePreserving.ae
    (ProphetSecretary.Model.Instance.clocks_pairwise_distinct (n := N))

end ProphetSecretary.Limiting
