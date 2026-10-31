import ProphetSecretary.Limiting.CountableClockLevelNull
import ProphetSecretary.Limiting.CountableClockNullSets

/-!
# Actual anonymous arrivals do not tie countable continuation values

For each independent whole-clock vector the equality set has null Poisson
intensity. The actual finite band laws and their independence from individual
clocks give one almost-sure statement for every present anonymous point.
Analytical band/array labels never enter the decision callback.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting.CountableInstance

lemma configuration_clockProfile_ne_ae (B : CountableInstance) (hZero : B.terminal = 0)
    (μ : FiniteMeasure ℝ) (clocks : ℕ → ℝ) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∀ᵐ ω ∂configurationLaw μ, ∀ j : Fin ω.1,
      B.clockProfile clocks none w c (ω.2 j).1 ≠ w*(ω.2 j).2 := by
  have hMap : Measurable (fun p : Point => (clocks,p.1)) := measurable_const.prodMk measurable_fst
  have hProfile := (B.measurable_clockProfile hw.le hc.le none).comp hMap
  change Measurable (fun p : Point => B.clockProfile clocks none w c p.1) at hProfile
  have hPoint : MeasurableSet {p : Point | B.clockProfile clocks none w c p.1 ≠ w*p.2} :=
    (measurableSet_eq_fun hProfile (measurable_snd.const_mul w)).compl
  have hSections : ∀ᵐ x ∂(μ : Measure ℝ), ∀ᵐ t ∂Model.Instance.uniformClock,
      B.clockProfile clocks none w c t ≠ w*x :=
    Eventually.of_forall (fun x => B.clockProfile_time_ne_ae hZero clocks none hw hc (w*x))
  have hIntensity : ∀ᵐ p ∂ProphetSecretary.Limiting.intensity μ, B.clockProfile clocks none w c p.1 ≠ w*p.2 :=
    (Measure.ae_prod_iff_ae_ae hPoint).mpr ((Measure.ae_ae_comm hPoint).mpr hSections)
  exact all_points_in_of_intensity_compl_null μ hPoint (ae_iff.mp hIntensity)

lemma measurableSet_configuration_clockProfile_regular (B : CountableInstance) {w c : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) :
    MeasurableSet {q : Configuration × (ℕ → ℝ) | ∀ j : ℕ, j < q.1.1 →
      B.clockProfile q.2 none w c (configurationPoint j q.1).1 ≠ w*(configurationPoint j q.1).2} := by
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  have hPresent : MeasurableSet {q : Configuration × (ℕ → ℝ) | j < q.1.1} :=
    (measurableSet_configurationPoint_present j).preimage measurable_fst
  have hPoint : Measurable (fun q : Configuration × (ℕ → ℝ) => configurationPoint j q.1) :=
    (measurable_configurationPoint j).comp measurable_fst
  have hMap : Measurable (fun q : Configuration × (ℕ → ℝ) => (q.2,(configurationPoint j q.1).1)) :=
    measurable_snd.prodMk (measurable_fst.comp hPoint)
  have hProfile := (B.measurable_clockProfile hw hc none).comp hMap
  change Measurable (fun q : Configuration × (ℕ → ℝ) => B.clockProfile q.2 none w c (configurationPoint j q.1).1) at hProfile
  have hValue : Measurable (fun q : Configuration × (ℕ → ℝ) => w*(configurationPoint j q.1).2) :=
    (measurable_snd.comp hPoint).const_mul w
  have hGood := (measurableSet_eq_fun hProfile hValue).compl
  have he : {q : Configuration × (ℕ → ℝ) | j < q.1.1 →
        B.clockProfile q.2 none w c (configurationPoint j q.1).1 ≠ w*(configurationPoint j q.1).2} =
      {q | ¬j < q.1.1} ∪ {q | B.clockProfile q.2 none w c (configurationPoint j q.1).1 ≠ w*(configurationPoint j q.1).2} := by
    ext q
    simp only [mem_setOf_eq,mem_union,imp_iff_not_or]
  rw [he]
  exact hPresent.compl.union hGood

lemma poisson_clockProfile_eval_ne_ae (B : CountableInstance) (hZero : B.terminal = 0) (Eval : CountableInstance)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂Eval.completeWorldLaw ν, ∀ k j : ℕ, j < (v.1 k).1 →
      B.clockProfile v.2.2.1 none w c (configurationPoint j (v.1 k)).1 ≠ w*(configurationPoint j (v.1 k)).2 := by
  have hOne (k : ℕ) : ∀ᵐ v ∂Eval.completeWorldLaw ν, ∀ j : ℕ, j < (v.1 k).1 →
      B.clockProfile v.2.2.1 none w c (configurationPoint j (v.1 k)).1 ≠ w*(configurationPoint j (v.1 k)).2 := by
    have hU : Measurable (fun z : (ℕ → ℝ) × ((ℕ → ℝ) × Seed) => z.2.1) := measurable_fst.comp measurable_snd
    have hI := (Eval.configuration_individual_world_independent ν).comp (measurable_pi_apply k) hU
    have hConfigMP : MeasurePreserving (fun v : CompleteWorld Seed => v.1 k) (Eval.completeWorldLaw ν)
        (configurationLaw (Eval.bandIntensity k)) := (Eval.bandConfiguration_measurePreserving k).comp measurePreserving_fst
    have hClock : Measurable (fun v : CompleteWorld Seed => v.2.2.1) :=
      (Eval.individualClocks_completeWorld_measurePreserving ν).measurable
    have hSections (clocks : ℕ → ℝ) : ∀ᵐ ω ∂configurationLaw (Eval.bandIntensity k), ∀ j : ℕ, j < ω.1 →
        B.clockProfile clocks none w c (configurationPoint j ω).1 ≠ w*(configurationPoint j ω).2 := by
      filter_upwards [B.configuration_clockProfile_ne_ae hZero (Eval.bandIntensity k) clocks hw hc] with ω hω
      intro j hj
      simpa only [configurationPoint,dif_pos hj] using hω ⟨j,hj⟩
    exact ProphetSecretary.Probability.indepFun_ae_of_sections hI hConfigMP.measurable hClock hConfigMP.hasLaw
      (B.measurableSet_configuration_clockProfile_regular hw.le hc.le) hSections
  exact ae_all_iff.mpr hOne

end ProphetSecretary.Limiting.CountableInstance
