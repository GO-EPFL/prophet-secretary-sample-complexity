import ProphetSecretary.Limiting.CountableMarkovThreshold
import ProphetSecretary.Limiting.CountableSelection
import ProphetSecretary.Limiting.CountableReach
import ProphetSecretary.Reach.AlmostEverywhereQuadraticReach

/-!
# Strict individual reach for full countable Markov thresholds

The actual Markov callbacks imply pending-infimum domination on every raw
vector. Replacing a uniform candidate clock preserves the full product law.
The proved integral minimization and Jensen inequality then yield the quadratic
selection term. Actual admissibility converts the analytical infimum back to
the executed duration only almost surely, avoiding any null-slice assumption.
Paper correspondence: `lem:monotone-reach`, `lem:strict-reach`,
`upbound:strict-reach`, individual-variable limiting-instance extension.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in
lemma CountableRule.pendingIndividualTime_replace_clock (π : CountableRule Seed) (i : ℕ)
    (z : CompleteWorld Seed × ℝ) :
    π.pendingIndividualTime i (replaceIndividualClock i z)=π.pendingIndividualTime i z.1 := by
  unfold CountableRule.pendingIndividualTime
  rw [keepIndividualPending_replace_clock]

theorem countableMarkovRule_strict_reach
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hAccept : DeletionMonotoneCountableAcceptance accept)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hAdm : (countableMarkovRule accept).Admissible B ν) (i : ℕ) :
    (countableMarkovRule accept).individualReachProbability B ν i-
      (∫ v, (countableMarkovRule accept).realizedDuration v ∂B.completeWorldLaw ν) ≥
      ((countableMarkovRule accept).individualSelectionProbability B ν i)^2/2 := by
  let π := countableMarkovRule accept
  let ρ := B.completeWorldLaw ν
  let σ := π.pendingIndividualTime i
  let d := π.infimumDuration
  let a₀ := π.individualSelectionIndicator i
  let a : CompleteWorld Seed × ℝ → ℝ := a₀ ∘ replaceIndividualClock i
  let τ : CompleteWorld Seed × ℝ → ℝ := d ∘ replaceIndividualClock i
  have hRep := replaceIndividualClock_measurePreserving B ν i
  have hσm : Measurable σ := π.measurable_pendingIndividualTime hπ i
  have hdm : Measurable d := π.measurable_infimumDuration hπ
  have ha₀m : Measurable a₀ := π.measurable_individualSelectionIndicator hπ i
  have ham : Measurable a := ha₀m.comp hRep.measurable
  have hσ01 : ∀ᵐ v ∂ρ, σ v ∈ Icc (0 : ℝ) 1 := Eventually.of_forall (π.pendingIndividualTime_bounds i)
  have hσI : Integrable σ ρ := π.integrable_pendingIndividualTime hπ B ν i
  have ha01 (z : CompleteWorld Seed × ℝ) : a z ∈ Icc (0 : ℝ) 1 :=
    π.individualSelectionIndicator_mem_unit i (replaceIndividualClock i z)
  have haI : Integrable a (ρ.prod Model.Instance.uniformClock) :=
    hRep.integrable_comp_of_integrable (π.integrable_individualSelectionIndicator hπ B ν i)
  have hτI : Integrable τ (ρ.prod Model.Instance.uniformClock) :=
    hRep.integrable_comp_of_integrable (π.integrable_infimumDuration hπ B ν)
  have hClock : ∀ᵐ z : CompleteWorld Seed × ℝ ∂ρ.prod Model.Instance.uniformClock,
      z.2 ∈ Icc (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := Model.Instance.uniformClock)).ae
      (ae_restrict_mem measurableSet_Icc)
  have hWI : Integrable (fun z : CompleteWorld Seed × ℝ => (σ z.1-z.2)*a z)
      (ρ.prod Model.Instance.uniformClock) := by
    apply Integrable.of_bound (((hσm.comp measurable_fst).sub measurable_snd).mul ham).aestronglyMeasurable 1
    filter_upwards [hClock] with z ht
    have hs := π.pendingIndividualTime_bounds i z.1
    have hDiff : ‖σ z.1-z.2‖ ≤ 1 := by
      rw [Real.norm_eq_abs,abs_le]
      constructor <;> linarith only [hs.1,hs.2,ht.1,ht.2]
    have hA : ‖a z‖ ≤ 1 := by rw [Real.norm_eq_abs,abs_of_nonneg (ha01 z).1]; exact (ha01 z).2
    change ‖(σ z.1-z.2)*a z‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul hDiff hA (norm_nonneg _) zero_le_one).trans (by norm_num)
  have hStop (v : CompleteWorld Seed) (t : ℝ) : τ (v,t) ≤ σ v := by
    have h := countableMarkovRule_infimum_le_pending accept hAccept i (replaceIndividualClock i (v,t))
    rw [π.pendingIndividualTime_replace_clock] at h
    exact h
  have hSelected (z : CompleteWorld Seed × ℝ) (hSel : π.SelectsIndividual (replaceIndividualClock i z) i) :
      τ z=z.2 := by
    have h := π.infimumDuration_eq_clock_of_selectsIndividual i (replaceIndividualClock i z) hSel
    simpa only [τ,d,Function.comp_apply,replaceIndividualClock,Function.update_self] using h
  have hSupport : ∀ᵐ v ∂ρ, ∀ t ∈ Ioo (σ v) 1, a (v,t)=0 := by
    apply Eventually.of_forall
    intro v t ht
    dsimp only [a,a₀,Function.comp_apply,CountableRule.individualSelectionIndicator]
    rw [if_neg]
    intro hSel
    have h := hStop v t
    rw [hSelected (v,t) hSel] at h
    exact (not_le.mpr ht.1) h
  have hGap : ∀ᵐ v ∂ρ, ∀ t ∈ Icc (0 : ℝ) 1, (σ v-t)*a (v,t) ≤ σ v-τ (v,t) := by
    apply Eventually.of_forall
    intro v t _ht
    dsimp only [a,a₀,Function.comp_apply,CountableRule.individualSelectionIndicator]
    split_ifs with hSel
    · rw [mul_one,hSelected (v,t) hSel]
    · rw [mul_zero]
      exact sub_nonneg.mpr (hStop v t)
  have hQuad := ProphetSecretary.Reach.quadratic_gap_product_ae ρ hσ01 hσI haI hτI hWI
    (Eventually.of_forall fun v t _ => ha01 (v,t)) hSupport hGap
  have hComp (f : CompleteWorld Seed → ℝ) (hf : Measurable f) :
      (∫ z, f (replaceIndividualClock i z) ∂ρ.prod Model.Instance.uniformClock)=∫ v, f v ∂ρ := by
    have h := integral_map (μ := ρ.prod Model.Instance.uniformClock) hRep.measurable.aemeasurable hf.aestronglyMeasurable
    rw [hRep.map_eq] at h
    exact h.symm
  have hAeq : (∫ z, a z ∂ρ.prod Model.Instance.uniformClock)=π.individualSelectionProbability B ν i := by
    change (∫ z, a₀ (replaceIndividualClock i z) ∂ρ.prod Model.Instance.uniformClock)=_
    rw [hComp a₀ ha₀m]
    exact π.integral_individualSelectionIndicator hπ B ν i
  have hTeq : (∫ z, τ z ∂ρ.prod Model.Instance.uniformClock)=∫ v, π.realizedDuration v ∂ρ :=
    (hComp d hdm).trans (integral_congr_ae (π.infimumDuration_eq_actual B ν hAdm))
  change (∫ z, a z ∂ρ.prod Model.Instance.uniformClock)^2/2 ≤
    (∫ v, σ v ∂ρ)-∫ z, τ z ∂ρ.prod Model.Instance.uniformClock at hQuad
  rw [hAeq,hTeq] at hQuad
  change π.individualSelectionProbability B ν i^2/2 ≤
    (∫ v, π.pendingIndividualTime i v ∂B.completeWorldLaw ν)-∫ v, π.realizedDuration v ∂B.completeWorldLaw ν at hQuad
  rw [← π.individualReachProbability_eq_mean_pending hπ B ν hAdm i] at hQuad
  exact hQuad

/-- The real-threshold class stated in the paper is a specialization of the
proved Markov acceptance comparison. -/
theorem countableThresholdRule_strict_reach
    (θ : Seed → IndividualMask → ℝ → Option ℕ → ℝ) (hθ : MonotoneCountableThresholds θ)
    (hπ : (countableThresholdRule θ).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (hAdm : (countableThresholdRule θ).Admissible B ν) (i : ℕ) :
    (countableThresholdRule θ).individualReachProbability B ν i-
      (∫ v, (countableThresholdRule θ).realizedDuration v ∂B.completeWorldLaw ν) ≥
      ((countableThresholdRule θ).individualSelectionProbability B ν i)^2/2 :=
  countableMarkovRule_strict_reach (fun r A t j x => decide (θ r A t j ≤ x))
    (thresholdAcceptance_deletionMonotone θ hθ) hπ B ν hAdm i

end ProphetSecretary.Limiting.CountableInstance
