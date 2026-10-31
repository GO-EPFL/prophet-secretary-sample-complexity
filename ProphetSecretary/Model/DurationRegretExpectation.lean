import ProphetSecretary.Model.ConditionalRegret

/-!
# Averaging the actual conditional regret

Clock replacement preserves the original instance, so the conditional pending
loss is exactly the corresponding reached Bellman loss in expectation. Its
measurability is proved from the original observer, with the policy design fixed.
-/

open MeasureTheory Set Filter
open scoped Classical Topology BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.measurable_durationActionLoss_worldClock (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (i : Fin n) :
    Measurable (fun v : World n Unit × ℝ ↦ P.durationActionLoss z z' i (v.1.1 i) v.1.2.1 v.2) := by
  let π : Policy Unit n := (P.valuePolicy hP zero_le_one hz).rule
  have hπ : π.IsMeasurable := (P.valuePolicy hP zero_le_one hz).measurable_rule
  have hu (j : Fin n) : Measurable (fun v : World n Unit × ℝ ↦ (Function.update v.1.2.1 i v.2) j) := by
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using (measurable_snd : Measurable (Prod.snd : World n Unit × ℝ → ℝ))
    · simpa only [Function.update_of_ne hji, Function.comp_def] using
        ((measurable_pi_apply j).comp ((measurable_fst.comp measurable_snd).comp measurable_fst))
  have h : Measurable (fun v : World n Unit × ℝ ↦
      π.arrivalBellmanLoss P 1 z' () v.1.1 (Function.update v.1.2.1 i v.2) i) :=
    π.measurable_arrivalBellmanLoss hπ P hP zero_lt_one hz' measurable_const
    (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_fst)) hu i
  convert h using 1
  funext v
  exact (P.valuePolicy_arrivalLoss_eq_durationActionLoss hP hz v.1.1 v.1.2.1 i v.2).symm

lemma Instance.measurable_pendingDurationLoss_worldClock (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (π : Policy Unit n) (hπ : π.IsMeasurable)
    {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (i : Fin n) :
    Measurable (fun v : World n Unit × ℝ ↦ if v.2 ≤ π.pendingTime () v.1.1 v.1.2.1 i then
      P.durationActionLoss z z' i (v.1.1 i) v.1.2.1 v.2 else 0) := by
  have hσ : Measurable (fun v : World n Unit × ℝ ↦ π.pendingTime () v.1.1 v.1.2.1 i) :=
    π.measurable_stoppingTime hπ measurable_const
      (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
      (fun j ↦ (measurable_pi_apply j).comp ((measurable_fst.comp measurable_snd).comp measurable_fst))
      (Finset.univ.erase i)
  exact Measurable.ite (measurableSet_le measurable_snd hσ)
    (P.measurable_durationActionLoss_worldClock hP hz hz' i) measurable_const

lemma Instance.measurable_conditionalDurationRegret (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (π : Policy Unit n) (hπ : π.IsMeasurable)
    {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (i : Fin n) :
    Measurable (fun ω : World n Unit ↦ P.conditionalDurationRegret π z z' ω.1 ω.2.1 i) := by
  exact (P.measurable_pendingDurationLoss_worldClock hP π hπ hz hz' i).stronglyMeasurable.integral_prod_right'.measurable

lemma Instance.integrable_pendingDurationLoss_worldClock (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (π : Policy Unit n) (hπ : π.IsMeasurable)
    {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (i : Fin n) :
    Integrable (fun v : World n Unit × ℝ ↦ if v.2 ≤ π.pendingTime () v.1.1 v.1.2.1 i then
      P.durationActionLoss z z' i (v.1.1 i) v.1.2.1 v.2 else 0)
      ((P.worldLaw (Measure.dirac ())).prod Instance.uniformClock) := by
  apply Integrable.of_bound (P.measurable_pendingDurationLoss_worldClock hP π hπ hz hz' i).aestronglyMeasurable |z - z'|
  filter_upwards [(Measure.quasiMeasurePreserving_snd
    (μ := P.worldLaw (Measure.dirac ())) (ν := Instance.uniformClock)).ae (ae_restrict_mem measurableSet_Icc)] with v hv
  by_cases hσ : v.2 ≤ π.pendingTime () v.1.1 v.1.2.1 i
  · simp only [if_pos hσ, Real.norm_eq_abs,
      abs_of_nonneg (P.durationActionLoss_nonnegative z z' i (v.1.1 i) v.1.2.1 v.2)]
    have hb := P.durationActionLoss_le_band hP hz hz' i (v.1.1 i) v.1.2.1 hv.1
    split_ifs at hb
    · exact hb
    · exact hb.trans (abs_nonneg _)
  · simp only [if_neg hσ, norm_zero, abs_nonneg]

noncomputable def Instance.canonicalReachedDurationLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 ≤ z) (z' : ℝ) (i : Fin n)
    (ω : World n Unit) : ℝ :=
  let π : Policy Unit n := (P.valuePolicy hP zero_le_one hz).rule
  if π.Reaches () ω.1 ω.2.1 i then π.arrivalBellmanLoss P 1 z' () ω.1 ω.2.1 i else 0

lemma Instance.measurable_canonicalReachedDurationLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (i : Fin n) :
    Measurable (P.canonicalReachedDurationLoss hP hz z' i) := by
  let π : Policy Unit n := (P.valuePolicy hP zero_le_one hz).rule
  have hπ : π.IsMeasurable := (P.valuePolicy hP zero_le_one hz).measurable_rule
  exact Measurable.ite (π.measurableSet_reaches hπ measurable_const
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i)
    (π.measurable_arrivalBellmanLoss hπ P hP zero_lt_one hz' measurable_const
      (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
      (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i) measurable_const

lemma Instance.canonicalReachedDurationLoss_replaceClock (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 ≤ z) (z' : ℝ) (i : Fin n)
    (v : World n Unit × ℝ) (ht : v.2 ≤ 1) :
    P.canonicalReachedDurationLoss hP hz z' i (Instance.replaceClock i v) =
      if v.2 ≤ (P.valuePolicy hP zero_le_one hz).rule.pendingTime () v.1.1 v.1.2.1 i then
        P.durationActionLoss z z' i (v.1.1 i) v.1.2.1 v.2 else 0 := by
  let π : Policy Unit n := (P.valuePolicy hP zero_le_one hz).rule
  have hr : π.Reaches () v.1.1 (Function.update v.1.2.1 i v.2) i ↔
      v.2 ≤ π.pendingTime () v.1.1 v.1.2.1 i := by
    rw [π.reaches_iff_le_pendingTime _ _ _ i (by simpa only [Function.update_self] using ht), Function.update_self]
    have he := Instance.pendingTime_replaceClock π i ((v.1.1, (v.1.2.1, ())), v.2)
    change π.pendingTime () v.1.1 (Function.update v.1.2.1 i v.2) i = π.pendingTime () v.1.1 v.1.2.1 i at he
    rw [he]
  change (if π.Reaches () v.1.1 (Function.update v.1.2.1 i v.2) i then
      π.arrivalBellmanLoss P 1 z' () v.1.1 (Function.update v.1.2.1 i v.2) i else 0) = _
  have hl : π.arrivalBellmanLoss P 1 z' () v.1.1 (Function.update v.1.2.1 i v.2) i =
      P.durationActionLoss z z' i (v.1.1 i) v.1.2.1 v.2 :=
    P.valuePolicy_arrivalLoss_eq_durationActionLoss hP hz v.1.1 v.1.2.1 i v.2
  simp only [hr, hl]
  rfl

lemma Instance.integrable_canonicalReachedDurationLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (i : Fin n) :
    Integrable (P.canonicalReachedDurationLoss hP hz z' i) (P.worldLaw (Measure.dirac ())) := by
  let π : Policy Unit n := (P.valuePolicy hP zero_le_one hz).rule
  have hπ : π.IsMeasurable := (P.valuePolicy hP zero_le_one hz).measurable_rule
  have hrep := P.replaceClock_measurePreserving (Measure.dirac ()) i
  apply (hrep.integrable_comp (P.measurable_canonicalReachedDurationLoss hP hz hz' i).aestronglyMeasurable).mp
  apply (P.integrable_pendingDurationLoss_worldClock hP π hπ hz hz' i).congr
  filter_upwards [(Measure.quasiMeasurePreserving_snd
    (μ := P.worldLaw (Measure.dirac ())) (ν := Instance.uniformClock)).ae (ae_restrict_mem measurableSet_Icc)] with v hv
  exact (P.canonicalReachedDurationLoss_replaceClock hP hz z' i v hv.2).symm

/-- Actual clock replacement and Fubini identify a reached arrival loss with
its pending-clock conditional regret. -/
theorem Instance.mean_conditionalDurationRegret (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (i : Fin n) :
    (∫ ω : World n Unit, P.conditionalDurationRegret (P.valuePolicy hP zero_le_one hz).rule
      z z' ω.1 ω.2.1 i ∂P.worldLaw (Measure.dirac ())) =
    ∫ ω : World n Unit, P.canonicalReachedDurationLoss hP hz z' i ω ∂P.worldLaw (Measure.dirac ()) := by
  let π : Policy Unit n := (P.valuePolicy hP zero_le_one hz).rule
  have hπ : π.IsMeasurable := (P.valuePolicy hP zero_le_one hz).measurable_rule
  let F := fun v : World n Unit × ℝ ↦ if v.2 ≤ π.pendingTime () v.1.1 v.1.2.1 i then
    P.durationActionLoss z z' i (v.1.1 i) v.1.2.1 v.2 else 0
  have hF := P.integrable_pendingDurationLoss_worldClock hP π hπ hz hz' i
  change Integrable F ((P.worldLaw (Measure.dirac ())).prod Instance.uniformClock) at hF
  change (∫ ω : World n Unit, ∫ t : ℝ, F (ω, t) ∂Instance.uniformClock ∂P.worldLaw (Measure.dirac ())) = _
  rw [← integral_prod F hF]
  have hrep := P.replaceClock_measurePreserving (Measure.dirac ()) i
  have hm := P.measurable_canonicalReachedDurationLoss hP hz hz' i
  have he := integral_map (μ := (P.worldLaw (Measure.dirac ())).prod Instance.uniformClock) hrep.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hrep.map_eq] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [(Measure.quasiMeasurePreserving_snd
    (μ := P.worldLaw (Measure.dirac ())) (ν := Instance.uniformClock)).ae (ae_restrict_mem measurableSet_Icc)] with v hv
  exact (P.canonicalReachedDurationLoss_replaceClock hP hz z' i v hv.2).symm

/-- The complete scalar regret is the sum of these conditional candidate-clock
integrals. The competitor is the fixed base canonical policy. -/
theorem Instance.durationRegret_eq_mean_conditional (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    optimalScalarValue P 1 z' - (P.valuePolicy hP zero_le_one hz).scalarObjective P 1 z' =
      ∑ i : Fin n, ∫ ω : World n Unit, P.conditionalDurationRegret
        (P.valuePolicy hP zero_le_one hz).rule z z' ω.1 ω.2.1 i ∂P.worldLaw (Measure.dirac ()) := by
  let C := P.valuePolicy hP zero_le_one hz
  rw [C.bellman_performanceDifference P hP zero_lt_one hz']
  change (∫ ω : World n Unit, C.rule.reachedBellmanLoss P 1 z' ω.2.2 ω.1 ω.2.1
    ∂P.worldLaw (Measure.dirac ())) = _
  have he : (fun ω : World n Unit ↦ C.rule.reachedBellmanLoss P 1 z' ω.2.2 ω.1 ω.2.1) =
      (fun ω ↦ ∑ i : Fin n, P.canonicalReachedDurationLoss hP hz z' i ω) := by
    funext ω
    have hr : ω.2.2 = () := Subsingleton.elim _ _
    rw [hr]
    rfl
  rw [he, integral_finsetSum Finset.univ (fun i _ ↦ P.integrable_canonicalReachedDurationLoss hP hz hz' i)]
  exact Finset.sum_congr rfl (fun i _ ↦ (P.mean_conditionalDurationRegret hP hz hz' i).symm)

end ProphetSecretary.Model
