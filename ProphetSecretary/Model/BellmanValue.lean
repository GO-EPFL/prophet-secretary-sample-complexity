import ProphetSecretary.Model.BellmanStep

/-!
# The finite Bellman first-step value

The functional averages the larger of the first acceptance payoff and optimal
additional child continuation, including accrued duration payoff. Its time
measure is derived from the independent uniform arrival law.
-/

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace ProphetSecretary.Model
namespace Instance

variable {n : ℕ}

lemma firstArrivalDensity_le_one (m : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    firstArrivalDensity m t ≤ 1 := by
  have hb : ENNReal.ofReal (1 - t) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (sub_le_self (1 : ℝ) ht.1)
  exact pow_le_one₀ (by positivity) hb

instance firstChildTimeLaw_finite (i : Fin (n + 1)) : IsFiniteMeasure (firstChildTimeLaw i) := by
  unfold firstChildTimeLaw
  apply isFiniteMeasure_withDensity
  have hbound : (∫⁻ t, firstArrivalDensity (remainingSet i).card t ∂uniformClock) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _t, (1 : ℝ≥0∞) ∂uniformClock :=
        lintegral_mono_ae ((ae_restrict_mem measurableSet_Icc).mono
          (fun t ht ↦ firstArrivalDensity_le_one _ ht))
      _ = 1 := by simp
  exact ne_top_of_le_ne_top (by simp) hbound

lemma firstChildTimeLaw_mem_unitInterval (i : Fin (n + 1)) :
    ∀ᵐ t ∂firstChildTimeLaw i, t ∈ Icc (0 : ℝ) 1 ∧ t < 1 := by
  apply (withDensity_absolutelyContinuous uniformClock (firstArrivalDensity (remainingSet i).card)).ae_le
  filter_upwards [ae_restrict_mem measurableSet_Icc, uniformClock.ae_ne 1] with t ht hne
  exact ⟨ht, lt_of_le_of_ne ht.2 hne⟩

/-- A total measurable extension of the optimal additional child value.
It agrees with `V(P_A;w,c(1-t))` on every actual first-arrival time. -/
noncomputable def bellmanContinuation (P : Instance (n + 1)) (i : Fin (n + 1)) (w c t : ℝ) : ℝ :=
  optimalScalarValue (P.restrictTo (remainingSet i)) w (c * max 0 (1 - t))

lemma bellmanContinuation_continuous (P : Instance (n + 1))
    (hP : Integrable maximum P.valuesLaw) (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Continuous (P.bellmanContinuation i w c) := by
  exact (optimalScalarValue_durationWeight_continuousOn (P.restrictTo (remainingSet i))
    (P.restrictTo_integrable_maximum _ hP) hw).comp_continuous
      (continuous_const.mul (continuous_const.max (continuous_const.sub continuous_id)))
      (fun _t ↦ mul_nonneg hc (le_max_left _ _))

lemma integrable_bellmanContinuation (P : Instance (n + 1))
    (hP : Integrable maximum P.valuesLaw) (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (P.bellmanContinuation i w c) (firstChildTimeLaw i) := by
  let Q := P.restrictTo (remainingSet i)
  apply Integrable.of_bound (P.bellmanContinuation_continuous hP i hw hc).measurable.aestronglyMeasurable
    (w * Q.expectedMaximum + c)
  filter_upwards [firstChildTimeLaw_mem_unitInterval i] with t ht
  have hcu0 : 0 ≤ c * max 0 (1 - t) := mul_nonneg hc (le_max_left _ _)
  have hcu1 : c * max 0 (1 - t) ≤ c := by
    apply (mul_le_mul_of_nonneg_left (max_le zero_le_one (sub_le_self 1 ht.1.1)) hc).trans_eq
    exact mul_one c
  have h0 := optimalScalarValue_nonnegative Q (P.restrictTo_integrable_maximum _ hP) hw hcu0
  have h1 := optimalScalarValue_le_benchmark Q (P.restrictTo_integrable_maximum _ hP) hw hcu0
  change ‖optimalScalarValue Q w (c * max 0 (1 - t))‖ ≤ w * Q.expectedMaximum + c
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1.trans (add_le_add le_rfl hcu1)

/-- Bellman payoff at first time and first observed value. -/
noncomputable def bellmanFirstPayoff (P : Instance (n + 1)) (i : Fin (n + 1)) (w c : ℝ)
    (z : ℝ × ℝ) : ℝ := c * z.1 + max (w * z.2) (P.bellmanContinuation i w c z.1)

lemma measurable_bellmanFirstPayoff (P : Instance (n + 1))
    (hP : Integrable maximum P.valuesLaw) (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Measurable (P.bellmanFirstPayoff i w c) := by
  exact (measurable_const.mul measurable_fst).add
    ((measurable_const.mul measurable_snd).max
      ((P.bellmanContinuation_continuous hP i hw hc).measurable.comp measurable_fst))

lemma integrable_bellmanFirstPayoff (P : Instance (n + 1))
    (hP : Integrable maximum P.valuesLaw) (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (P.bellmanFirstPayoff i w c) ((firstChildTimeLaw i).prod (P.law i)) := by
  have ht : Integrable (id : ℝ → ℝ) (firstChildTimeLaw i) := by
    apply Integrable.of_bound aestronglyMeasurable_id 1
    filter_upwards [firstChildTimeLaw_mem_unitInterval i] with t h01
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg h01.1.1] using h01.1.2
  have hx := (P.integrable_maximum_iff.mp hP) i
  exact ((ht.const_mul c).comp_fst (P.law i)).add
    (((hx.const_mul w).comp_snd (firstChildTimeLaw i)).sup
      ((P.integrable_bellmanContinuation hP i hw hc).comp_fst (P.law i)))

noncomputable def bellmanValue (P : Instance (n + 1)) (w c : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), ∫ z, P.bellmanFirstPayoff i w c z ∂(firstChildTimeLaw i).prod (P.law i)

end Instance
end ProphetSecretary.Model
