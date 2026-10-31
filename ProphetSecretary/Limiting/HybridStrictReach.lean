import ProphetSecretary.Limiting.HybridMarkovThreshold
import ProphetSecretary.Limiting.HybridSelection
import ProphetSecretary.Reach.AlmostEverywhereQuadraticReach

/-!
# Strict quadratic reach comparison for retained hybrid identities

For an admissible count-hidden Markov threshold rule monotone under adding
retained unseen identities, qᵢ−Eτ≥(pᵢˢᵉˡ)²/2. Pending domination is derived
from the actual thresholds, and independence from the candidate value and
clock was constructed separately. The integral minimization and Jensen steps
are the proved almost-sure quadratic comparison, applied to actual selection.
This is the finite-intensity retained-variable extension only.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

/-- The retained-variable strict part of `lem:monotone-reach` =
`lem:strict-reach`, including independent auxiliary policy randomness. -/
theorem hybridThresholdRule_strict_reach
    (θ : Seed → Finset (Fin n) → ℝ → Option (Fin n) → ℝ) (hθ : MonotoneHybridThresholds θ)
    (hπ : (hybridThresholdRule θ).IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (hybridThresholdRule θ).individualReachProbability P μ ν i - (hybridThresholdRule θ).meanDuration P μ ν ≥
      ((hybridThresholdRule θ).individualSelectionProbability P μ ν i) ^ 2 / 2 := by
  let π := hybridThresholdRule θ
  let ρ := hybridWorldLaw P μ ν
  let σ := π.pendingIndividualTime i
  let d := π.realizedDuration
  let a₀ := π.retainedSelectionIndicator i
  let a : HybridWorld n Seed × ℝ → ℝ := a₀ ∘ replaceIndividualClock i
  let τ : HybridWorld n Seed × ℝ → ℝ := d ∘ replaceIndividualClock i
  have hrep := replaceIndividualClock_measurePreserving P μ ν i
  have hσm : Measurable σ := π.measurable_pendingIndividualTime hπ i
  have hdm : Measurable d := π.measurable_realizedDuration hπ
  have ha₀m : Measurable a₀ := π.measurable_retainedSelectionIndicator hπ i
  have ham : Measurable a := ha₀m.comp hrep.measurable
  have hσ01 : ∀ᵐ v ∂ρ, σ v ∈ Icc (0 : ℝ) 1 := π.pendingIndividualTime_mem_unit P μ ν i
  have hσI : Integrable σ ρ := π.integrable_pendingIndividualTime hπ P μ ν i
  have ha01 (z : HybridWorld n Seed × ℝ) : a z ∈ Icc (0 : ℝ) 1 :=
    π.retainedSelectionIndicator_mem_unit i (replaceIndividualClock i z)
  have haI : Integrable a (ρ.prod Model.Instance.uniformClock) := by
    apply Integrable.of_bound ham.aestronglyMeasurable 1
    exact Eventually.of_forall fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (ha01 z).1]; exact (ha01 z).2
  have hτI : Integrable τ (ρ.prod Model.Instance.uniformClock) :=
    hrep.integrable_comp_of_integrable (π.integrable_realizedDuration hπ P μ ν)
  have hclock : ∀ᵐ z : HybridWorld n Seed × ℝ ∂ρ.prod Model.Instance.uniformClock, z.2 ∈ Icc (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := Model.Instance.uniformClock)).ae (ae_restrict_mem measurableSet_Icc)
  have hσprod : ∀ᵐ z : HybridWorld n Seed × ℝ ∂ρ.prod Model.Instance.uniformClock, σ z.1 ∈ Icc (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst (μ := ρ) (ν := Model.Instance.uniformClock)).ae hσ01
  have hWI : Integrable (fun z : HybridWorld n Seed × ℝ => (σ z.1-z.2) * a z) (ρ.prod Model.Instance.uniformClock) := by
    apply Integrable.of_bound (((hσm.comp measurable_fst).sub measurable_snd).mul ham).aestronglyMeasurable 1
    filter_upwards [hclock,hσprod] with z ht hs
    have hdiff : ‖σ z.1-z.2‖ ≤ 1 := by
      rw [Real.norm_eq_abs,abs_le]
      constructor <;> linarith [hs.1,hs.2,ht.1,ht.2]
    have hnorm : ‖a z‖ ≤ 1 := by rw [Real.norm_eq_abs,abs_of_nonneg (ha01 z).1]; exact (ha01 z).2
    change ‖(σ z.1-z.2) * a z‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul hdiff hnorm (norm_nonneg _) zero_le_one).trans (by norm_num)
  have hpoissonTimes := (Measure.quasiMeasurePreserving_fst (μ := configurationLaw μ) (ν := P.worldLaw ν)).ae
    (configuration_times_mem_Ioo μ)
  have hretainedTimes := (Measure.quasiMeasurePreserving_snd (μ := configurationLaw μ) (ν := P.worldLaw ν)).ae
    (P.world_clocks_mem_unitInterval ν)
  have hstop : ∀ᵐ v ∂ρ, ∀ t ∈ Icc (0 : ℝ) 1, τ (v,t) ≤ σ v := by
    filter_upwards [hpoissonTimes,hretainedTimes] with v hp hr t ht
    have hc : ∀ k : Fin (n+v.1.1), combinedClocks (Function.update v.2.2.1 i t) v.1.2 k ∈ Icc (0 : ℝ) 1 := by
      intro k
      induction k using Fin.addCases with
      | left j =>
        by_cases hji : j = i
        · subst j
          simpa only [combinedClocks,Fin.addCases_left,Function.update_self] using ht
        · simpa only [combinedClocks,Fin.addCases_left,Function.update_of_ne hji] using hr j
      | right j =>
        simpa only [combinedClocks,Fin.addCases_right] using ⟨(hp j).1.le,(hp j).2.le⟩
    have hc' : ∀ k : Fin (n+(replaceIndividualClock i (v,t)).1.1),
        combinedClocks (replaceIndividualClock i (v,t)).2.2.1 (replaceIndividualClock i (v,t)).1.2 k ∈ Icc (0 : ℝ) 1 := hc
    have hdom := hybridThresholdRule_duration_le_pending θ hθ i (replaceIndividualClock i (v,t)) hc'
    rw [π.pendingIndividualTime_replace] at hdom
    exact hdom
  have hselected (z : HybridWorld n Seed × ℝ)
      (hz : π.SelectsIndividual (replaceIndividualClock i z).2.2.2 (replaceIndividualClock i z).2.1
        (replaceIndividualClock i z).2.2.1 (replaceIndividualClock i z).1 i) : τ z = z.2 := by
    have h := π.duration_eq_clock_of_selectsIndividual i (replaceIndividualClock i z) hz
    simpa only [τ,d,Function.comp_apply,replaceIndividualClock,Model.Instance.replaceClock,Function.update_self] using h
  have hsupport : ∀ᵐ v ∂ρ, ∀ t ∈ Ioo (σ v) 1, a (v,t) = 0 := by
    filter_upwards [hstop,hσ01] with v hv hσ t ht
    dsimp [a,a₀,HybridRule.retainedSelectionIndicator]
    rw [if_neg]
    intro hsel
    have hs := hv t ⟨hσ.1.trans ht.1.le,ht.2.le⟩
    rw [hselected (v,t) hsel] at hs
    exact (not_le.mpr ht.1) hs
  have hgap : ∀ᵐ v ∂ρ, ∀ t ∈ Icc (0 : ℝ) 1, (σ v-t) * a (v,t) ≤ σ v-τ (v,t) := by
    filter_upwards [hstop] with v hv t ht
    dsimp [a,a₀,HybridRule.retainedSelectionIndicator]
    split_ifs with hsel
    · rw [mul_one,hselected (v,t) hsel]
    · rw [mul_zero]
      exact sub_nonneg.mpr (hv t ht)
  have hquad := ProphetSecretary.Reach.quadratic_gap_product_ae ρ hσ01 hσI haI hτI hWI
    (Eventually.of_forall fun v t _ => ha01 (v,t)) hsupport hgap
  have hcomp (f : HybridWorld n Seed → ℝ) (hf : Measurable f) :
      (∫ z, f (replaceIndividualClock i z) ∂ρ.prod Model.Instance.uniformClock) = ∫ v, f v ∂ρ := by
    have he := integral_map (μ := ρ.prod Model.Instance.uniformClock) hrep.measurable.aemeasurable hf.aestronglyMeasurable
    rw [hrep.map_eq] at he
    exact he.symm
  have hAeq : (∫ z, a z ∂ρ.prod Model.Instance.uniformClock) = π.individualSelectionProbability P μ ν i := by
    change (∫ z, a₀ (replaceIndividualClock i z) ∂ρ.prod Model.Instance.uniformClock) = _
    rw [hcomp a₀ ha₀m]
    exact π.integral_retainedSelectionIndicator hπ P μ ν i
  have hTeq : (∫ z, τ z ∂ρ.prod Model.Instance.uniformClock) = π.meanDuration P μ ν := hcomp d hdm
  change (∫ z, a z ∂ρ.prod Model.Instance.uniformClock)^2 / 2 ≤
    (∫ v, σ v ∂ρ) - ∫ z, τ z ∂ρ.prod Model.Instance.uniformClock at hquad
  rw [hAeq,hTeq] at hquad
  change π.individualSelectionProbability P μ ν i ^ 2 / 2 ≤
    (∫ v, π.pendingIndividualTime i v ∂hybridWorldLaw P μ ν) - π.meanDuration P μ ν at hquad
  rw [← π.individualReachProbability_eq_mean_pending hπ P μ ν i] at hquad
  exact hquad

end ProphetSecretary.Limiting
