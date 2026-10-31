import ProphetSecretary.Model.BellmanResidualBasic
import ProphetSecretary.Model.ClockReplacement

/-!
# Candidate-clock disintegration of reached Bellman losses

The competing policy may use the full observed past and independent auxiliary
randomness. Replacing one clock preserves the actual product instance law; the
pending-run representation is proved afterwards from coordinate erasure.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma measurable_clockReplacement (i : Fin n) :
    Measurable (Instance.replaceClock i : World n Seed × ℝ → World n Seed) := by
  have hU : Measurable (fun v : World n Seed × ℝ ↦ Function.update v.1.2.1 i v.2) := by
    apply measurable_pi_lambda
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using (measurable_snd : Measurable (Prod.snd : World n Seed × ℝ → ℝ))
    · simpa only [Function.update_of_ne hji, Function.comp_def] using
        ((measurable_pi_apply j).comp (measurable_fst.snd.fst))
  exact measurable_fst.fst.prodMk (hU.prodMk measurable_fst.snd.snd)

noncomputable def Policy.reachedArrivalBellmanLoss (π : Policy Seed n) (Q : Instance n) (w c : ℝ)
    (i : Fin n) (ω : World n Seed) : ℝ :=
  if π.Reaches ω.2.2 ω.1 ω.2.1 i then π.arrivalBellmanLoss Q w c ω.2.2 ω.1 ω.2.1 i else 0

omit [MeasurableSpace Seed] in
lemma Policy.reachedArrivalBellmanLoss_nonnegative (π : Policy Seed n) (Q : Instance n)
    (w c : ℝ) (i : Fin n) (ω : World n Seed) : 0 ≤ π.reachedArrivalBellmanLoss Q w c i ω := by
  unfold Policy.reachedArrivalBellmanLoss
  split_ifs
  · exact π.arrivalBellmanLoss_nonnegative Q w c _ _ _ i
  · exact le_rfl

lemma Policy.measurable_reachedArrivalBellmanLoss (π : Policy Seed n) (hπ : π.IsMeasurable) (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (i : Fin n) :
    Measurable (π.reachedArrivalBellmanLoss Q w c i) :=
  Measurable.ite (π.measurableSet_reaches hπ (measurable_snd.comp measurable_snd)
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i)
    (π.measurable_arrivalBellmanLoss hπ Q hQ hw hc (measurable_snd.comp measurable_snd)
      (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
      (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i) measurable_const

lemma Policy.integrable_reachedArrivalBellmanLoss (π : Policy Seed n) (hπ : π.IsMeasurable) (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (i : Fin n) :
    Integrable (π.reachedArrivalBellmanLoss Q w c i) (P.worldLaw ν) := by
  apply (π.integrable_reachedBellmanLoss_under hπ Q P hQ hP ν hw hc).mono'
    (π.measurable_reachedArrivalBellmanLoss hπ Q hQ hw hc i).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (π.reachedArrivalBellmanLoss_nonnegative Q w c i ω)]
    exact Finset.single_le_sum (fun j _ ↦ π.reachedArrivalBellmanLoss_nonnegative Q w c j ω) (Finset.mem_univ i))

noncomputable def Policy.clockConditionalBellmanLoss (π : Policy Seed n) (Q : Instance n)
    (w c : ℝ) (i : Fin n) (ω : World n Seed) : ℝ :=
  ∫ t : ℝ, π.reachedArrivalBellmanLoss Q w c i (Instance.replaceClock i (ω, t)) ∂Instance.uniformClock

lemma Policy.measurable_clockConditionalBellmanLoss (π : Policy Seed n) (hπ : π.IsMeasurable) (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (i : Fin n) :
    Measurable (π.clockConditionalBellmanLoss Q w c i) :=
  ((π.measurable_reachedArrivalBellmanLoss hπ Q hQ hw hc i).comp (measurable_clockReplacement i)).stronglyMeasurable.integral_prod_right'.measurable

lemma Policy.integrable_clockConditionalBellmanLoss (π : Policy Seed n) (hπ : π.IsMeasurable) (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (i : Fin n) :
    Integrable (π.clockConditionalBellmanLoss Q w c i) (P.worldLaw ν) :=
  ((P.replaceClock_measurePreserving ν i).integrable_comp_of_integrable
    (π.integrable_reachedArrivalBellmanLoss hπ Q P hQ hP ν hw hc i)).integral_prod_left

/-- Exact expectation identity for every general randomized observer. The design
law and the online evaluation law are distinct fixed inputs. -/
theorem Policy.mean_clockConditionalBellmanLoss (π : Policy Seed n) (hπ : π.IsMeasurable) (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (i : Fin n) :
    (∫ ω, π.clockConditionalBellmanLoss Q w c i ω ∂P.worldLaw ν) =
      ∫ ω, π.reachedArrivalBellmanLoss Q w c i ω ∂P.worldLaw ν := by
  have hrep := P.replaceClock_measurePreserving ν i
  have hInt := hrep.integrable_comp_of_integrable (π.integrable_reachedArrivalBellmanLoss hπ Q P hQ hP ν hw hc i)
  let F := fun v : World n Seed × ℝ ↦ π.reachedArrivalBellmanLoss Q w c i (Instance.replaceClock i v)
  change Integrable F ((P.worldLaw ν).prod Instance.uniformClock) at hInt
  change (∫ ω : World n Seed, ∫ t : ℝ, F (ω, t) ∂Instance.uniformClock ∂P.worldLaw ν) = _
  rw [← integral_prod F hInt]
  have he := integral_map (μ := (P.worldLaw ν).prod Instance.uniformClock) hrep.measurable.aemeasurable
    (π.measurable_reachedArrivalBellmanLoss hπ Q hQ hw hc i).aestronglyMeasurable
  rw [hrep.map_eq] at he
  exact he.symm

omit [MeasurableSpace Seed] in
/-- The auxiliary execution erases the candidate's clock before checking reach.
This is a pointwise execution equality, not an independence assumption. -/
lemma Policy.reachedArrivalBellmanLoss_replaceClock_pending (π : Policy Seed n) (Q : Instance n)
    (w c : ℝ) (i : Fin n) (ω : World n Seed) {t : ℝ} (ht : t ≤ 1) :
    π.reachedArrivalBellmanLoss Q w c i (Instance.replaceClock i (ω, t)) =
      if t ≤ π.pendingTime ω.2.2 ω.1 ω.2.1 i then π.arrivalBellmanLoss Q w c ω.2.2 ω.1 (Function.update ω.2.1 i t) i else 0 := by
  have hr : π.Reaches ω.2.2 ω.1 (Function.update ω.2.1 i t) i ↔ t ≤ π.pendingTime ω.2.2 ω.1 ω.2.1 i := by
    rw [π.reaches_iff_le_pendingTime _ _ _ i (by simpa only [Function.update_self] using ht), Function.update_self]
    have he := Instance.pendingTime_replaceClock π i (ω, t)
    change π.pendingTime ω.2.2 ω.1 (Function.update ω.2.1 i t) i = π.pendingTime ω.2.2 ω.1 ω.2.1 i at he
    rw [he]
  change (if π.Reaches ω.2.2 ω.1 (Function.update ω.2.1 i t) i then
    π.arrivalBellmanLoss Q w c ω.2.2 ω.1 (Function.update ω.2.1 i t) i else 0) = _
  simp only [hr]

omit [MeasurableSpace Seed] in
lemma Policy.clockConditionalBellmanLoss_nonnegative (π : Policy Seed n) (Q : Instance n)
    (w c : ℝ) (i : Fin n) (ω : World n Seed) : 0 ≤ π.clockConditionalBellmanLoss Q w c i ω :=
  integral_nonneg (fun t ↦ π.reachedArrivalBellmanLoss_nonnegative Q w c i (Instance.replaceClock i (ω, t)))

theorem Policy.integral_reachedBellmanLoss_eq_sum_clockConditional (π : Policy Seed n) (hπ : π.IsMeasurable)
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ ω : World n Seed, π.reachedBellmanLoss Q w c ω.2.2 ω.1 ω.2.1 ∂P.worldLaw ν) =
      ∑ i : Fin n, ∫ ω : World n Seed, π.clockConditionalBellmanLoss Q w c i ω ∂P.worldLaw ν := by
  have he : (fun ω : World n Seed ↦ π.reachedBellmanLoss Q w c ω.2.2 ω.1 ω.2.1) =
      (fun ω ↦ ∑ i : Fin n, π.reachedArrivalBellmanLoss Q w c i ω) := by funext ω; rfl
  rw [he, integral_finsetSum Finset.univ (fun i _ ↦ π.integrable_reachedArrivalBellmanLoss hπ Q P hQ hP ν hw hc i)]
  exact Finset.sum_congr rfl (fun i _ ↦ (π.mean_clockConditionalBellmanLoss hπ Q P hQ hP ν hw hc i).symm)

omit [MeasurableSpace Seed] in
lemma Policy.clockConditionalBellmanLoss_eq_pending (π : Policy Seed n) (Q : Instance n)
    (w c : ℝ) (i : Fin n) (ω : World n Seed) :
    π.clockConditionalBellmanLoss Q w c i ω =
      ∫ t : ℝ, if t ≤ π.pendingTime ω.2.2 ω.1 ω.2.1 i then
        π.arrivalBellmanLoss Q w c ω.2.2 ω.1 (Function.update ω.2.1 i t) i else 0 ∂Instance.uniformClock := by
  unfold Policy.clockConditionalBellmanLoss
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact π.reachedArrivalBellmanLoss_replaceClock_pending Q w c i ω ht.2

end ProphetSecretary.Model
