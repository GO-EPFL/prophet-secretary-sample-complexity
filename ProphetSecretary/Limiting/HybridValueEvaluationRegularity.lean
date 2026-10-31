import ProphetSecretary.Limiting.HybridValueTieNull
import ProphetSecretary.Limiting.PoissonBranchNullTransfer

/-!
# Regularity of fixed canonical hybrid callbacks under an evaluation law

The design determining continuation thresholds is fixed. Evaluation offers
may have different independent distributions. Independent uniform clocks and
the design's strict positive-cost time monotonicity exclude ties for every
real current value, including atoms and normalized zero-intensity marks.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology Classical
namespace ProphetSecretary.Limiting
variable {n N : ℕ}

lemma FiniteIntensityHybridInstance.thresholdRegular_pointLaw_ae
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (μ : FiniteMeasure ℝ) :
    ∀ᵐ p ∂pointLaw μ, ∀ A i, p.2≠B.valueHybridThreshold w c () A p.1 i := by
  have hs : ∀ᵐ x ∂(μ.normalize:Measure ℝ), ∀ᵐ t ∂Model.Instance.uniformClock,
      ∀ A i, x≠B.valueHybridThreshold w c () A t i := Eventually.of_forall (B.thresholdTime_ne_ae ha hw hc)
  have hE := B.measurableSet_thresholdRegular hw.le hc.le
  exact (Measure.ae_prod_iff_ae_ae hE).mpr ((Measure.ae_ae_comm hE).mpr hs)

lemma FiniteIntensityHybridInstance.individual_threshold_eval_branch_ae
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (N : ℕ) (i : Fin n) :
    ∀ᵐ q ∂(arrayLaw μ N).prod (P.worldLaw (Measure.dirac ())), ∀ A j,
      q.2.1 i≠B.valueHybridThreshold w c () A (q.2.2.1 i) j := by
  have hBase := (P.values_clocksSeed_independent (Measure.dirac ())).comp
    (measurable_pi_apply i) ((measurable_pi_apply i).comp measurable_fst)
  have hXi : Measurable (fun z : Model.World n Unit => z.1 i) := by fun_prop
  have hTi : Measurable (fun z : Model.World n Unit => z.2.1 i) := by fun_prop
  have hPull := Model.indepFun_pullback
    (measurePreserving_snd : MeasurePreserving (Prod.snd : (Fin N → Point) × Model.World n Unit → Model.World n Unit)
      ((arrayLaw μ N).prod (P.worldLaw (Measure.dirac ()))) (P.worldLaw (Measure.dirac ()))) hXi hTi hBase
  have hClock := (P.world_clock_measurePreserving (Measure.dirac ()) i).comp
    (measurePreserving_snd (μ := arrayLaw μ N) (ν := P.worldLaw (Measure.dirac ())))
  exact ProphetSecretary.Probability.indepFun_ae_of_sections hPull.symm hClock.measurable
    (by fun_prop) hClock.hasLaw (B.measurableSet_thresholdRegular hw.le hc.le) (B.thresholdTime_ne_ae ha hw hc)

/-- Fixed-count arrival regularity for the design's callback under arbitrary
independent evaluation offers. Both reward and elapsed stopping time are used. -/
theorem FiniteIntensityHybridInstance.valueRule_eval_branch_outcomes_continuousAt_ae
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (N : ℕ) :
    ∀ᵐ q ∂(arrayLaw μ N).prod (P.worldLaw (Measure.dirac ())),
      ContinuousAt (fun z : (Fin (n+N) → ℝ) × (Fin (n+N) → ℝ) =>
        ((B.valueRule w c).asFinitePolicy N).reward () Finset.univ z.1 z.2)
        (combinedValues q.2.1 q.1,combinedClocks q.2.2.1 q.1) ∧
      ContinuousAt (fun z : (Fin (n+N) → ℝ) × (Fin (n+N) → ℝ) =>
        ((B.valueRule w c).asFinitePolicy N).stoppingTime () Finset.univ z.1 z.2)
        (combinedValues q.2.1 q.1,combinedClocks q.2.2.1 q.1) := by
  have hRet := ae_all_iff.mpr (fun i : Fin n => B.individual_threshold_eval_branch_ae ha hw hc P μ N i)
  have hCfg : ∀ᵐ q ∂(arrayLaw μ N).prod (P.worldLaw (Measure.dirac ())), ∀ j : Fin N, ∀ A i,
      (q.1 j).2≠B.valueHybridThreshold w c () A (q.1 j).1 i := by
    rw [ae_all_iff]
    intro j
    have hPoint : MeasurePreserving (fun q : (Fin N → Point) × Model.World n Unit => q.1 j)
        ((arrayLaw μ N).prod (P.worldLaw (Measure.dirac ()))) (pointLaw μ) :=
      (measurePreserving_eval (fun _ : Fin N => pointLaw μ) j).comp measurePreserving_fst
    exact hPoint.quasiMeasurePreserving.ae (B.thresholdRegular_pointLaw_ae ha hw hc μ)
  filter_upwards [hRet,hCfg,hybridArray_combined_clocks_regular P μ (Measure.dirac ()) N] with q hRet hCfg hClock
  have hTie (k : Fin (n+N)) (A : Finset (Fin (n+N))) :
      combinedValues q.2.1 q.1 k≠finiteHybridThreshold (B.valueHybridThreshold w c) N () A
        (combinedClocks q.2.2.1 q.1 k) k := by
    induction k using Fin.addCases with
    | left i =>
      simpa only [combinedValues,combinedClocks,finiteHybridThreshold,Fin.addCases_left] using hRet i (retainedUnseen A) (some i)
    | right j =>
      simpa only [combinedValues,combinedClocks,finiteHybridThreshold,Fin.addCases_right] using hCfg j (retainedUnseen A) none
  exact hybridThresholdRule_finite_outcomes_continuousAt (B.valueHybridThreshold w c) N ()
    (fun A i => B.valueHybridThreshold_continuous hw.le hc.le A i) Finset.univ
    (combinedValues q.2.1 q.1) (combinedClocks q.2.2.1 q.1) hClock.1
    (fun i => ne_of_lt (hClock.2 i).2) (fun i => hTie i _)
end ProphetSecretary.Limiting
