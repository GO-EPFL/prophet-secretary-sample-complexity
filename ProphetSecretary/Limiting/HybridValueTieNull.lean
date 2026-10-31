import ProphetSecretary.Limiting.HybridPositiveLevelSets
import ProphetSecretary.Probability.IndependentNullSections
import ProphetSecretary.Limiting.HybridClockNullSets
import ProphetSecretary.Limiting.HybridThresholdContinuity

/-!
# Actual finite-hybrid continuation thresholds have no arrival ties

Uniform candidate clocks make every retained threshold equality null, even
when its value has atoms. The same deterministic null clock sections give a
null subset of the actual Poisson intensity; Campbell's identity then excludes
all such anonymous points. These are properties of the constructed rule, not
an assumed policy interface or a conclusion inferred from value convergence.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma FiniteIntensityHybridInstance.measurableSet_thresholdRegular (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    MeasurableSet {p : Point | ∀ A i, p.2 ≠ B.valueHybridThreshold w c () A p.1 i} := by
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro A
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_eq_fun measurable_snd ((B.valueHybridThreshold_continuous hw hc A i).measurable.comp measurable_fst)).compl

lemma FiniteIntensityHybridInstance.thresholdRegular_intensity_ae (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∀ᵐ p ∂ProphetSecretary.Limiting.intensity B.intensity, ∀ A i, p.2 ≠ B.valueHybridThreshold w c () A p.1 i := by
  have hs : ∀ᵐ x ∂(B.intensity : Measure ℝ), ∀ᵐ t ∂Model.Instance.uniformClock,
      ∀ A i, x ≠ B.valueHybridThreshold w c () A t i := Eventually.of_forall (B.thresholdTime_ne_ae ha hw hc)
  have hE := B.measurableSet_thresholdRegular hw.le hc.le
  exact (Measure.ae_prod_iff_ae_ae hE).mpr ((Measure.ae_ae_comm hE).mpr hs)

lemma FiniteIntensityHybridInstance.configuration_threshold_ne_ae (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∀ᵐ ω ∂configurationLaw B.intensity, ∀ j : Fin ω.1, ∀ A i,
      (ω.2 j).2 ≠ B.valueHybridThreshold w c () A (ω.2 j).1 i := by
  exact all_points_in_of_intensity_compl_null B.intensity (B.measurableSet_thresholdRegular hw.le hc.le)
    (ae_iff.mp (B.thresholdRegular_intensity_ae ha hw hc))

lemma FiniteIntensityHybridInstance.individual_threshold_ne_ae (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    ∀ᵐ v ∂B.law ν, ∀ A j, v.2.1 i ≠ B.valueHybridThreshold w c () A (v.2.2.1 i) j := by
  have hBase := (B.individuals.values_clocksSeed_independent ν).comp
    (measurable_pi_apply i) ((measurable_pi_apply i).comp measurable_fst)
  have hXi : Measurable (fun z : Model.World n Seed => z.1 i) := by fun_prop
  have hTi : Measurable (fun z : Model.World n Seed => z.2.1 i) := by fun_prop
  have hPull := Model.indepFun_pullback
    (measurePreserving_snd : MeasurePreserving (Prod.snd : HybridWorld n Seed → Model.World n Seed)
      (B.law ν) (B.individuals.worldLaw ν)) hXi hTi hBase
  have hClock := individualClock_measurePreserving B.individuals B.intensity ν i
  exact ProphetSecretary.Probability.indepFun_ae_of_sections hPull.symm hClock.measurable
    (by fun_prop) hClock.hasLaw (B.measurableSet_thresholdRegular hw.le hc.le) (B.thresholdTime_ne_ae ha hw hc)

/-- There are no threshold ties for any actual offer and any finite retained
state. The state of the executed observable history is included. -/
theorem FiniteIntensityHybridInstance.valueRule_all_states_threshold_ne_ae
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∀ᵐ v ∂B.law (Measure.dirac ()), ∀ k : Fin (n+v.1.1), ∀ A : Finset (Fin (n+v.1.1)),
      combinedValues v.2.1 v.1.2 k ≠ finiteHybridThreshold (B.valueHybridThreshold w c) v.1.1 () A
        (combinedClocks v.2.2.1 v.1.2 k) k := by
  have hRet : ∀ᵐ v ∂B.law (Measure.dirac ()), ∀ i : Fin n, ∀ A j,
      v.2.1 i ≠ B.valueHybridThreshold w c () A (v.2.2.1 i) j :=
    ae_all_iff.mpr (fun i => B.individual_threshold_ne_ae ha hw hc (Measure.dirac ()) i)
  have hCfg : ∀ᵐ v ∂B.law (Measure.dirac ()), ∀ j : Fin v.1.1, ∀ A i,
      (v.1.2 j).2 ≠ B.valueHybridThreshold w c () A (v.1.2 j).1 i :=
    (Measure.quasiMeasurePreserving_fst (μ := configurationLaw B.intensity)
      (ν := B.individuals.worldLaw (Measure.dirac ()))).ae (B.configuration_threshold_ne_ae ha hw hc)
  filter_upwards [hRet,hCfg] with v hvRet hvCfg
  intro k A
  induction k using Fin.addCases with
  | left i =>
    simpa only [combinedValues,combinedClocks,finiteHybridThreshold,Fin.addCases_left] using hvRet i (retainedUnseen A) (some i)
  | right j =>
    simpa only [combinedValues,combinedClocks,finiteHybridThreshold,Fin.addCases_right] using hvCfg j (retainedUnseen A) none

/-- Branchwise raw reward and duration are continuous at actual worlds. This
is independent of the still separate verification of value-rule optimality. -/
theorem FiniteIntensityHybridInstance.valueRule_outcomes_continuousAt_ae
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∀ᵐ v ∂B.law (Measure.dirac ()),
      ContinuousAt (fun z : (Fin (n+v.1.1) → ℝ) × (Fin (n+v.1.1) → ℝ) =>
        ((B.valueRule w c).asFinitePolicy v.1.1).reward () Finset.univ z.1 z.2)
        (combinedValues v.2.1 v.1.2,combinedClocks v.2.2.1 v.1.2) ∧
      ContinuousAt (fun z : (Fin (n+v.1.1) → ℝ) × (Fin (n+v.1.1) → ℝ) =>
        ((B.valueRule w c).asFinitePolicy v.1.1).stoppingTime () Finset.univ z.1 z.2)
        (combinedValues v.2.1 v.1.2,combinedClocks v.2.2.1 v.1.2) := by
  filter_upwards [B.valueRule_all_states_threshold_ne_ae ha hw hc,
    hybrid_combined_clocks_regular B.individuals B.intensity (Measure.dirac ())] with v hTie hClock
  exact hybridThresholdRule_finite_outcomes_continuousAt (B.valueHybridThreshold w c) v.1.1 ()
    (fun A i => B.valueHybridThreshold_continuous hw.le hc.le A i) Finset.univ
    (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) hClock.1
    (fun i => ne_of_lt (hClock.2 i).2) (fun i => hTie i _)

end ProphetSecretary.Limiting
