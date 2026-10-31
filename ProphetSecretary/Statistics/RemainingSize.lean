import ProphetSecretary.Statistics.ObservedCriticalPrefixes
import ProphetSecretary.Stability.TerminalWindow

/-!
# Mean size remaining at a deterministic clock time

All currently pending identities contribute their marginal first moments.
Uniform clocks give exactly (1−t)(1+S) for the mean size including remaining
time. The size decreases pathwise, independently of training and stopping.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.remainingSize (P : Instance n) (t : ℝ) (u : Fin n → ℝ) : ℝ :=
  (P.restrictTo (ProphetSecretary.Probability.pendingClockSet t u)).totalFirstMoment + (1-t)

lemma Instance.totalFirstMoment_restrictTo_mono (P : Instance n)
    {A B : Finset (Fin n)} (hAB : A ⊆ B) :
    (P.restrictTo A).totalFirstMoment ≤ (P.restrictTo B).totalFirstMoment := by
  have h := (P.restrictTo B).totalFirstMoment_restrictBy_le (stateInclusion hAB)
  rw [P.restrictTo_restrictBy hAB] at h
  exact h

lemma Instance.remainingSize_antitone (P : Instance n) (u : Fin n → ℝ) : Antitone (fun t => P.remainingSize t u) := by
  intro s t hst
  have hsub : ProphetSecretary.Probability.pendingClockSet t u ⊆ ProphetSecretary.Probability.pendingClockSet s u := by
    intro i hi
    exact (ProphetSecretary.Probability.mem_pendingClockSet s u i).mpr
      (hst.trans ((ProphetSecretary.Probability.mem_pendingClockSet t u i).mp hi))
  have h := P.totalFirstMoment_restrictTo_mono hsub
  unfold remainingSize
  linarith only [h,hst]

lemma Instance.pendingFirstMoment_all_eq_sum (P : Instance n) (t : ℝ) (u : Fin n → ℝ) :
    (P.restrictTo (ProphetSecretary.Probability.pendingClockSet t u)).totalFirstMoment =
      ∑ i, if t ≤ u i then (∫ x, x ∂P.law i) else 0 := by
  change (∑ j : Fin (ProphetSecretary.Probability.pendingClockSet t u).card,
    (∫ x, x ∂P.law (stateEmbedding (ProphetSecretary.Probability.pendingClockSet t u) j))) = _
  have he := sum_stateEmbedding_futureSuffix (ProphetSecretary.Probability.pendingClockSet t u)
    (fun i => ∫ x, x ∂P.law i)
  exact he.trans (Finset.sum_filter _ _)

lemma Instance.measurable_remainingSize (P : Instance n) (t : ℝ) : Measurable (P.remainingSize t) :=
  (measurable_of_finite (fun A : Finset (Fin n) => (P.restrictTo A).totalFirstMoment + (1-t))).comp
    (ProphetSecretary.Probability.measurable_pendingClockSet t)

lemma Instance.integrable_remainingSize (P : Instance n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (P.remainingSize t) (Instance.clocksLaw n) := by
  apply Integrable.of_bound (P.measurable_remainingSize t).aestronglyMeasurable (P.totalFirstMoment+1)
  exact Eventually.of_forall fun u => by
    have h := P.observedRemainingSize_mem ht0 ht1 u
    have h0 : 0 ≤ P.remainingSize t u := h.1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h.2

/-- Exact deterministic-time expectation used to bound grid entrance sizes. -/
theorem Instance.integral_remainingSize (P : Instance n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ u, P.remainingSize t u ∂Instance.clocksLaw n) = (1-t) * (P.totalFirstMoment+1) := by
  have hm (i : Fin n) : MeasurableSet {u : Fin n → ℝ | t ≤ u i} :=
    measurableSet_le measurable_const (measurable_pi_apply i)
  have hI (i : Fin n) : Integrable (fun u : Fin n → ℝ => if t ≤ u i then (∫ x, x ∂P.law i) else 0)
      (Instance.clocksLaw n) := (integrable_const _).indicator (hm i)
  have he (i : Fin n) : (∫ u : Fin n → ℝ, if t ≤ u i then (∫ x, x ∂P.law i) else 0 ∂Instance.clocksLaw n) =
      (1-t) * (∫ x, x ∂P.law i) := by
    have hp : MeasurePreserving (fun u : Fin n → ℝ => u i) (Instance.clocksLaw n) Instance.uniformClock :=
      measurePreserving_eval (fun _ : Fin n => Instance.uniformClock) i
    have hprob := map_measureReal_apply (μ := Instance.clocksLaw n) hp.measurable (s := Ici t) measurableSet_Ici
    rw [hp.map_eq, Instance.uniformClock_probability_ge ht0 ht1] at hprob
    change 1-t = (Instance.clocksLaw n).real {u : Fin n → ℝ | t ≤ u i} at hprob
    have hind := integral_indicator_const (μ := Instance.clocksLaw n) (∫ x, x ∂P.law i) (hm i)
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, ← hprob] using hind
  unfold remainingSize
  simp_rw [P.pendingFirstMoment_all_eq_sum]
  rw [integral_add (integrable_finsetSum _ (fun i _ => hI i)) (integrable_const _),
    integral_finsetSum _ (fun i _ => hI i)]
  simp only [he, integral_const, probReal_univ, one_smul]
  rw [← Finset.mul_sum]
  change (1-t) * P.totalFirstMoment + (1-t) = _
  ring

end ProphetSecretary.Model
