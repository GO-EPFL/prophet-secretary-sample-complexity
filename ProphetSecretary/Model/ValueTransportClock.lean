import ProphetSecretary.Model.ValueTransportStates
import ProphetSecretary.Model.PositiveCountBands

/-!
# Clock-integrated loss of a value perturbation

The actual canonical mapped loss is integrated over an independently replaced
candidate clock. Positive-count growth bounds its support band; a zero offer
has zero loss almost surely. Paper correspondence: `upmom:transport`.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Policy.measurable_mappedArrivalLoss {Seed Ω : Type*} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (π : Policy Seed n) (hπ : π.IsMeasurable) (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    {r : Ω → Seed} {x u : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ i, Measurable fun ω => x ω i) (hu : ∀ i, Measurable fun ω => u ω i) (i : Fin n) :
    Measurable (fun ω => π.mappedArrivalLoss Q f w c (r ω) (x ω) (u ω) i) := by
  have hX : Measurable (fun ω => w * f i (x ω i)) := measurable_const.mul ((hf i).comp (hx i))
  have hV := Q.measurable_continuationAtArrival hQ hw hc hx hu i
  have he : MeasurableSet {ω | π.action (r ω) Finset.univ (x ω) (u ω) i = true} :=
    measurableSet_eq_fun (π.measurable_action hπ hr hx hu Finset.univ i) measurable_const
  exact (hX.max hV).sub (Measurable.ite he hX hV)

theorem Instance.canonical_mappedLoss_clock_bound (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h w c : ℝ} (hh : 0 ≤ h) (hw : 0 < w) (hc : 0 < c)
    (hdispl : ∀ i a, |f i a - a| ≤ h) (x u : Fin n → ℝ) (i : Fin n) :
    let π := thresholdPolicy (fun (_ : Unit) A t j => P.valueThreshold w c A t j)
    (∫ t, π.mappedArrivalLoss (P.mapValues f hf hnn) f w c () x (Function.update u i t) i
      ∂Instance.uniformClock) ≤ 32 * w ^ 2 * h ^ 2 * (1 + P.positiveCount) / c := by
  let π := thresholdPolicy (fun (_ : Unit) A t j => P.valueThreshold w c A t j)
  let loss : ℝ → ℝ := fun t => π.mappedArrivalLoss (P.mapValues f hf hnn) f w c () x (Function.update u i t) i
  have hπ : π.IsMeasurable := P.valueThreshold_policy_isMeasurable hP hw.le hc.le
  have hQ := P.mapValues_integrable_of_bounded_displacement hP f hf hnn
    (fun j => Eventually.of_forall (hdispl j))
  have hu (j : Fin n) : Measurable (fun t : ℝ => Function.update u i t j) := by
    by_cases hj : j = i
    · subst j
      have heq : (fun t : ℝ => Function.update u i t i) = id := by
        funext t
        exact Function.update_self i t u
      rw [heq]
      exact measurable_id
    · simpa only [Function.update_of_ne hj] using (measurable_const : Measurable (fun _ : ℝ => u j))
  have hM : Measurable loss := π.measurable_mappedArrivalLoss hπ _ hQ f hf hw hc.le
    (r := fun _ : ℝ => ()) (x := fun _ : ℝ => x) (u := fun t : ℝ => Function.update u i t)
    measurable_const (fun _ => measurable_const) hu i
  have hL : 0 ≤ P.positiveCount := P.tailCount_nonnegative 0
  have hB : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      loss t ≤ (ProphetSecretary.Analysis.thresholdBand (P.candidateGap w c i (x i) u) (2 * w * h)).indicator
        (fun _ => 2 * w * h) t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hb := P.canonical_mappedLoss_band hP f hf hnn hh hw hc.le hdispl x (Function.update u i t) i
    by_cases hband : |P.candidateGap w c i (x i) u t| ≤ 2 * w * h
    · have hm : t ∈ ProphetSecretary.Analysis.thresholdBand (P.candidateGap w c i (x i) u) (2 * w * h) := ⟨ht, hband⟩
      rw [Set.indicator_of_mem hm]
      exact hb.1
    · have hm : t ∉ ProphetSecretary.Analysis.thresholdBand (P.candidateGap w c i (x i) u) (2 * w * h) :=
        fun hm => hband hm.2
      rw [Set.indicator_of_notMem hm]
      have heq := hb.2 (by
        rw [← P.candidateGap_eq_replacedAcceptanceGap w c i x u t]
        exact lt_of_not_ge hband)
      exact heq.le
  have hInt := ProphetSecretary.Analysis.integral_local_loss_le (loss := loss)
    (by positivity : 0 < c / (4 * (1 + P.positiveCount))) (by positivity : 0 ≤ 2 * w * h)
    (P.measurable_candidateGap hP hw.le hc.le i (x i) u)
    (P.candidateGap_positiveCount_slope hP hw hc i (x i) u) hM.aestronglyMeasurable
    (Eventually.of_forall fun t => π.mappedArrivalLoss_nonnegative _ f w c () x (Function.update u i t) i) hB
  change (∫ t, loss t ∂Instance.uniformClock) ≤ _
  apply hInt.trans_eq
  rw [div_div_eq_mul_div]
  ring

lemma Instance.canonical_mappedLoss_clock_zero (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hdispl : ∀ i a, |f i a - a| ≤ h) (hfzero : ∀ i, f i 0 = 0)
    (x u : Fin n → ℝ) (i : Fin n) (hi : x i = 0) :
    let π := thresholdPolicy (fun (_ : Unit) A t j => P.valueThreshold w c A t j)
    (∫ t, π.mappedArrivalLoss (P.mapValues f hf hnn) f w c () x (Function.update u i t) i
      ∂Instance.uniformClock) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc, Instance.uniformClock.ae_ne 1] with t ht hne
  exact P.canonical_mappedLoss_zero_offer hP f hf hnn hw hc hdispl hfzero x (Function.update u i t) i hi
    (by simpa only [Function.update_self] using lt_of_le_of_ne ht.2 hne)

end ProphetSecretary.Model
