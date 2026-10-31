import ProphetSecretary.Model.ValueTransportClock
import ProphetSecretary.Model.MappedRewardPerformance

/-!
# Averaging the transport loss

Independent candidate-clock replacement turns the pathwise band estimate into
a per-marginal bound proportional to its positive probability. Summing yields
the positive-count constant in `upmom:transport`, rather than an n factor.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem Instance.canonical_mappedLoss_mean_bound (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h w c : ℝ} (hh : 0 ≤ h) (hw : 0 < w) (hc : 0 < c)
    (hdispl : ∀ i a, |f i a - a| ≤ h) (hfzero : ∀ i, f i 0 = 0) (i : Fin n) :
    let π := thresholdPolicy (fun (_ : Unit) A t j => P.valueThreshold w c A t j)
    (∫ ω : World n Unit, π.mappedArrivalLoss (P.mapValues f hf hnn) f w c () ω.1 ω.2.1 i
      ∂P.worldLaw (Measure.dirac ())) ≤
      (32 * w ^ 2 * h ^ 2 * (1 + P.positiveCount) / c) * (P.law i).real (Ioi 0) := by
  let π := thresholdPolicy (fun (_ : Unit) A t j => P.valueThreshold w c A t j)
  let μ := P.worldLaw (Measure.dirac ())
  let K := 32 * w ^ 2 * h ^ 2 * (1 + P.positiveCount) / c
  let F : World n Unit → ℝ := fun ω => π.mappedArrivalLoss (P.mapValues f hf hnn) f w c () ω.1 ω.2.1 i
  let g : ℝ → ℝ := (Ioi 0).indicator (fun _ => K)
  have hπ : π.IsMeasurable := P.valueThreshold_policy_isMeasurable hP hw.le hc.le
  have hQ := P.mapValues_integrable_of_bounded_displacement hP f hf hnn
    (fun j => Eventually.of_forall (hdispl j))
  have hF : Measurable F := π.measurable_mappedArrivalLoss hπ _ hQ f hf hw hc.le
    (r := fun _ : World n Unit => ()) (x := Prod.fst) (u := fun ω => ω.2.1)
    measurable_const (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hFI : Integrable F μ := by
    apply Integrable.of_bound hF.aestronglyMeasurable (2 * w * h)
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (π.mappedArrivalLoss_nonnegative _ f w c () ω.1 ω.2.1 i)]
      exact (P.canonical_mappedLoss_band hP f hf hnn hh hw hc.le hdispl ω.1 ω.2.1 i).1
  have hp : MeasurePreserving (fun ω : World n Unit => ω.1 i) μ (P.law i) :=
    (measurePreserving_eval P.law i).comp measurePreserving_fst
  have hg : Measurable g := measurable_const.indicator measurableSet_Ioi
  have hgI : Integrable g (P.law i) := (integrable_const K).indicator measurableSet_Ioi
  have hgi : Integrable (fun ω : World n Unit => g (ω.1 i)) μ := hp.integrable_comp_of_integrable hgI
  have hclock := P.replaceClock_measurePreserving (Measure.dirac ()) i
  have hprod := hclock.integrable_comp_of_integrable hFI
  have heq := integral_map (μ := μ.prod Instance.uniformClock) hclock.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hclock.map_eq] at heq
  have hinner : ∀ᵐ ω : World n Unit ∂μ,
      (∫ t, F (Instance.replaceClock i (ω, t)) ∂Instance.uniformClock) ≤ g (ω.1 i) := by
    filter_upwards [hp.quasiMeasurePreserving.ae (P.nonnegative i)] with ω hx
    by_cases hpos : 0 < ω.1 i
    · change (∫ t, π.mappedArrivalLoss _ f w c () ω.1 (Function.update ω.2.1 i t) i
        ∂Instance.uniformClock) ≤ g (ω.1 i)
      rw [show g (ω.1 i) = K from Set.indicator_of_mem hpos _]
      exact P.canonical_mappedLoss_clock_bound hP f hf hnn hh hw hc hdispl ω.1 ω.2.1 i
    · have hz : ω.1 i = 0 := le_antisymm (not_lt.mp hpos) hx
      have hzero := P.canonical_mappedLoss_clock_zero hP f hf hnn hw hc hdispl hfzero ω.1 ω.2.1 i hz
      change (∫ t, π.mappedArrivalLoss _ f w c () ω.1 (Function.update ω.2.1 i t) i
        ∂Instance.uniformClock) ≤ g (ω.1 i)
      rw [hzero, show g (ω.1 i) = 0 from Set.indicator_of_notMem hpos _]
  have hmean := integral_mono_ae hprod.integral_prod_left hgi hinner
  have hfub := integral_prod (fun z : World n Unit × ℝ => F (Instance.replaceClock i z)) hprod
  have hsource : (∫ ω, F ω ∂μ) ≤ ∫ ω : World n Unit, g (ω.1 i) ∂μ :=
    heq.trans hfub |>.le.trans hmean
  have hmap := integral_map (μ := μ) hp.measurable.aemeasurable hg.aestronglyMeasurable
  rw [hp.map_eq] at hmap
  have hgmean : (∫ a, g a ∂P.law i) = K * (P.law i).real (Ioi 0) := by
    simpa only [g, smul_eq_mul, mul_comm] using
      integral_indicator_const K (show MeasurableSet (Ioi (0 : ℝ)) from measurableSet_Ioi) (μ := P.law i)
  exact hsource.trans_eq (hmap.symm.trans hgmean)

/-- Summing the actual reached losses yields L(1+L), with no additional
cardinality factor. Zero-valued observations remain in every execution. -/
theorem Instance.canonical_mappedReachedLoss_mean_bound (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h w c : ℝ} (hh : 0 ≤ h) (hw : 0 < w) (hc : 0 < c)
    (hdispl : ∀ i a, |f i a - a| ≤ h) (hfzero : ∀ i, f i 0 = 0) :
    let π := thresholdPolicy (fun (_ : Unit) A t j => P.valueThreshold w c A t j)
    (∫ ω : World n Unit, π.mappedReachedLoss (P.mapValues f hf hnn) f w c () ω.1 ω.2.1
      ∂P.worldLaw (Measure.dirac ())) ≤
      (32 * w ^ 2 * h ^ 2 * (1 + P.positiveCount) / c) * P.positiveCount := by
  let π := thresholdPolicy (fun (_ : Unit) A t j => P.valueThreshold w c A t j)
  let Q := P.mapValues f hf hnn
  let μ := P.worldLaw (Measure.dirac ())
  let F : Fin n → World n Unit → ℝ := fun i ω => π.mappedArrivalLoss Q f w c () ω.1 ω.2.1 i
  let K := 32 * w ^ 2 * h ^ 2 * (1 + P.positiveCount) / c
  have hπ : π.IsMeasurable := P.valueThreshold_policy_isMeasurable hP hw.le hc.le
  have hQ := P.mapValues_integrable_of_bounded_displacement hP f hf hnn
    (fun j => Eventually.of_forall (hdispl j))
  have hFI (i : Fin n) : Integrable (F i) μ := by
    have hm : Measurable (F i) := π.measurable_mappedArrivalLoss hπ Q hQ f hf hw hc.le
      (r := fun _ : World n Unit => ()) (x := Prod.fst) (u := fun ω => ω.2.1)
      measurable_const (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
    apply Integrable.of_bound hm.aestronglyMeasurable (2 * w * h)
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (π.mappedArrivalLoss_nonnegative Q f w c () ω.1 ω.2.1 i)]
      exact (P.canonical_mappedLoss_band hP f hf hnn hh hw hc.le hdispl ω.1 ω.2.1 i).1
  have hReached : Integrable (fun ω : World n Unit => π.mappedReachedLoss Q f w c () ω.1 ω.2.1) μ := by
    have hI := ((P.valuePolicy hP hw.le hc.le).mapped_bellman_performance Q P hQ hP f hf hnn hh hw hc.le hdispl).1
    exact hI
  have hsumI : Integrable (fun ω => ∑ i, F i ω) μ := integrable_finsetSum _ (fun i _ => hFI i)
  have hpoint (ω : World n Unit) : π.mappedReachedLoss Q f w c () ω.1 ω.2.1 ≤ ∑ i, F i ω := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hr : π.Reaches () ω.1 ω.2.1 i
    · simp only [if_pos hr]; exact le_rfl
    · simp only [if_neg hr]
      exact π.mappedArrivalLoss_nonnegative Q f w c () ω.1 ω.2.1 i
  calc
    _ ≤ ∫ ω, ∑ i, F i ω ∂μ := integral_mono hReached hsumI hpoint
    _ = ∑ i, ∫ ω, F i ω ∂μ := integral_finsetSum _ (fun i _ => hFI i)
    _ ≤ ∑ i, K * (P.law i).real (Ioi 0) := Finset.sum_le_sum fun i _ =>
      P.canonical_mappedLoss_mean_bound hP f hf hnn hh hw hc hdispl hfzero i
    _ = _ := by rw [← Finset.mul_sum]; rfl

end ProphetSecretary.Model
