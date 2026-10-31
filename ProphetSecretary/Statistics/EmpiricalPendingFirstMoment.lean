import ProphetSecretary.Statistics.EmpiricalFirstMoment

/-!
# Empirical pending means averaged over training and independent clocks

For every deterministic elapsed time t∈[0,1], the empirical first moment of
the actual unseen set has expectation (1−t)S. This combines the proved
unbiased sample mean with the actual independent training/clock product law,
and is the empirical-mean step of `upstat:tiny`.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.empirical_pendingFirstMoment_integral (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (fun q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      ((totalEmpiricalInstance (reservoirCoordinates.symm q.1)).restrictTo
        (ProphetSecretary.Probability.pendingClockSet t q.2)).totalFirstMoment)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
      ((totalEmpiricalInstance (reservoirCoordinates.symm q.1)).restrictTo
        (ProphetSecretary.Probability.pendingClockSet t q.2)).totalFirstMoment
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) = (1 - t) * P.totalFirstMoment := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  let M := fun (i : Fin n) (y : (Fin n × Fin k) → ℝ) =>
    ∫ x, x ∂(totalEmpiricalInstance (reservoirCoordinates.symm y)).law i
  let F := fun (i : Fin n) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) =>
    if t ≤ q.2 i then M i q.1 else 0
  have hC (i : Fin n) : MeasurableSet {q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) | t ≤ q.2 i} :=
    measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_snd)
  have hFI (i : Fin n) : Integrable (F i) μ :=
    ((P.integrable_empirical_coordinate_firstMoment hP i).comp_fst (Instance.clocksLaw n)).indicator (hC i)
  have heq : (fun q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      ((totalEmpiricalInstance (reservoirCoordinates.symm q.1)).restrictTo
        (ProphetSecretary.Probability.pendingClockSet t q.2)).totalFirstMoment) =
      (fun q => ∑ i, F i q) := by
    funext q
    exact (totalEmpiricalInstance (reservoirCoordinates.symm q.1)).pendingFirstMoment_all_eq_sum t q.2
  have hmean (i : Fin n) : (∫ q, F i q ∂μ) = (1 - t) * (∫ x, x ∂P.law i) := by
    have hf : (F i) = (fun q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
        M i q.1 * (if t ≤ q.2 i then (1 : ℝ) else 0)) := by
      funext q
      dsimp [F]
      split_ifs <;> simp
    have hclock : (∫ u : Fin n → ℝ, if t ≤ u i then (1 : ℝ) else 0 ∂Instance.clocksLaw n) = 1 - t := by
      have hp : MeasurePreserving (fun u : Fin n → ℝ => u i) (Instance.clocksLaw n) Instance.uniformClock :=
        measurePreserving_eval (fun _ : Fin n => Instance.uniformClock) i
      have hm := map_measureReal_apply (μ := Instance.clocksLaw n) hp.measurable (s := Ici t) measurableSet_Ici
      rw [hp.map_eq, Instance.uniformClock_probability_ge ht0 ht1] at hm
      change 1 - t = (Instance.clocksLaw n).real {u : Fin n → ℝ | t ≤ u i} at hm
      have hi := integral_indicator_one (μ := Instance.clocksLaw n)
        (measurableSet_le measurable_const (measurable_pi_apply i) : MeasurableSet {u : Fin n → ℝ | t ≤ u i})
      simpa only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using hi.trans hm.symm
    rw [hf]
    calc
      _ = (∫ y, M i y ∂P.trainingCoordinateLaw k) *
          (∫ u : Fin n → ℝ, if t ≤ u i then (1 : ℝ) else 0 ∂Instance.clocksLaw n) :=
        integral_prod_mul (μ := P.trainingCoordinateLaw k) (ν := Instance.clocksLaw n)
          (M i) (fun u => if t ≤ u i then (1 : ℝ) else 0)
      _ = _ := by
        change (∫ y : (Fin n × Fin k) → ℝ,
          (∫ x, x ∂(totalEmpiricalInstance (reservoirCoordinates.symm y)).law i) ∂P.trainingCoordinateLaw k) * _ = _
        rw [P.integral_empirical_coordinate_firstMoment hP i, hclock]
        ring
  rw [heq]
  refine ⟨integrable_finsetSum _ (fun i _ => hFI i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hFI i)]
  simp_rw [hmean]
  rw [← Finset.mul_sum]
  rfl

omit [NeZero k] in
/-- The true pending mean on the same training/clock product space. -/
theorem Instance.true_pendingFirstMoment_integral (P : Instance n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Integrable (fun q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (P.restrictTo (ProphetSecretary.Probability.pendingClockSet t q.2)).totalFirstMoment)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
      (P.restrictTo (ProphetSecretary.Probability.pendingClockSet t q.2)).totalFirstMoment
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) = (1 - t) * P.totalFirstMoment := by
  let G : (Fin n → ℝ) → ℝ := fun u => (P.restrictTo (ProphetSecretary.Probability.pendingClockSet t u)).totalFirstMoment
  have heq : G = (fun u => P.remainingSize t u - (1 - t)) := by
    funext u
    dsimp [G, Instance.remainingSize]
    ring
  have hGI : Integrable G (Instance.clocksLaw n) := by
    rw [heq]
    exact (P.integrable_remainingSize ht0 ht1).sub (integrable_const _)
  have hmean : (∫ u, G u ∂Instance.clocksLaw n) = (1 - t) * P.totalFirstMoment := by
    rw [heq, integral_sub (P.integrable_remainingSize ht0 ht1) (integrable_const _), P.integral_remainingSize ht0 ht1]
    simp only [integral_const, probReal_univ, one_smul]
    ring
  have hprod := integral_fun_snd (μ := P.trainingCoordinateLaw k) (ν := Instance.clocksLaw n) G
  simp only [probReal_univ, one_smul] at hprod
  exact ⟨hGI.comp_snd (P.trainingCoordinateLaw k), hprod.trans hmean⟩

end ProphetSecretary.Model
