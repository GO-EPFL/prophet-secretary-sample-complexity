import ProphetSecretary.Limiting.HybridRewardTailPathwise
import ProphetSecretary.Limiting.HybridReachValue
import ProphetSecretary.Limiting.HybridScalarObjectives

/-!
# General-policy reward versus duration and positive tail counts

Retained reached-tail probabilities factor by the derived value independence;
q_i≤2Eτ bounds them. The actual Mecke compensator bounds anonymous reached
points by intensity times Eτ. The resulting constant is independent of the
retained dimension and applies before any optimizer is known to exist.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma HybridRule.measurable_retainedTailReachIndicator (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (i : Fin n) (b : ℝ) : Measurable (π.retainedTailReachIndicator i b) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact (π.measurableSet_reachesIndividual hπ i).inter
    (measurableSet_lt measurable_const ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))

lemma HybridRule.integrable_retainedTailReachIndicator (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) (b : ℝ) :
    Integrable (π.retainedTailReachIndicator i b) (hybridWorldLaw P μ ν) := by
  apply Integrable.of_bound (π.measurable_retainedTailReachIndicator hπ i b).aestronglyMeasurable 1
  apply ae_of_all
  intro v
  unfold HybridRule.retainedTailReachIndicator
  split_ifs <;> norm_num

lemma HybridRule.integral_retainedTailReachIndicator (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) (b : ℝ) :
    (∫ v, π.retainedTailReachIndicator i b v ∂hybridWorldLaw P μ ν) =
      π.individualReachProbability P μ ν i*(P.law i).real (Ioi b) := by
  have hE : MeasurableSet {v : HybridWorld n Seed | π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i ∧ b < v.2.1 i} :=
    (π.measurableSet_reachesIndividual hπ i).inter
      (measurableSet_lt measurable_const ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
  have hI : (∫ v, π.retainedTailReachIndicator i b v ∂hybridWorldLaw P μ ν) =
      (hybridWorldLaw P μ ν).real {v | π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i ∧ b < v.2.1 i} := by
    simpa only [HybridRule.retainedTailReachIndicator,Set.indicator_apply,Set.mem_setOf_eq,Pi.one_apply] using integral_indicator_one hE
  exact hI.trans (π.reachedIndividualTailProbability_eq hπ P μ ν i b)

noncomputable def FiniteIntensityHybridInstance.tailCount (B : FiniteIntensityHybridInstance n) (b : ℝ) : ℝ :=
  B.individuals.tailCount b+(B.intensity : Measure ℝ).real (Ioi b)

lemma FiniteIntensityHybridInstance.tailCount_nonnegative (B : FiniteIntensityHybridInstance n) (b : ℝ) :
    0 ≤ B.tailCount b := add_nonneg (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg) measureReal_nonneg

/-- General competing policies, including independent auxiliary randomness.
The terminal reward must be at most the cutoff; terminal0 satisfies this for
every nonnegative cutoff. -/
theorem RandomizedHybridPolicy.expectedReward_le_cutoff_add_tailCount
    (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n) {b : ℝ}
    (hb : 0 ≤ b) (ha : (B.terminal : ℝ) ≤ b) :
    π.expectedReward B ≤ b+2*π.expectedDuration B*(B.cap : ℝ)*B.tailCount b := by
  let J := fun i => π.rule.retainedTailReachIndicator i b
  let K := fun v => (π.rule.reachedPoissonBandCount (Ioi b) v).toReal
  have hJI (i : Fin n) : Integrable (J i) (B.law π.seedLaw) :=
    π.rule.integrable_retainedTailReachIndicator π.measurable_rule B.individuals B.intensity π.seedLaw i b
  have hKI : Integrable K (B.law π.seedLaw) :=
    π.rule.integrable_reachedPoissonBandCount π.measurable_rule B.individuals B.intensity π.seedLaw measurableSet_Ioi
  have hSumI : Integrable (fun v => (∑ i, J i v)+K v) (B.law π.seedLaw) :=
    (integrable_finsetSum Finset.univ fun i _ => hJI i).add hKI
  have hVal := realized_values_bounds B.individuals B.intensity π.seedLaw B.individual_bounded B.intensity_supported
  have hR := integral_mono_ae (π.integrable_reward B)
    ((integrable_const b).add (hSumI.const_mul (B.cap : ℝ))) (by
      filter_upwards [hVal] with v hv
      exact π.rule.reward_le_cutoff_add_reached_tails B.terminal b B.cap ha hb B.cap.property v (fun i => (hv i).2))
  change π.expectedReward B ≤ ∫ v, b+(B.cap : ℝ)*((∑ i, J i v)+K v) ∂B.law π.seedLaw at hR
  rw [integral_add (integrable_const _) (hSumI.const_mul _),integral_const_mul,
    integral_add (integrable_finsetSum Finset.univ fun i _ => hJI i) hKI,
    integral_finsetSum Finset.univ fun i _ => hJI i,integral_const] at hR
  simp only [probReal_univ,one_smul] at hR
  have hJ (i : Fin n) : (∫ v, J i v ∂B.law π.seedLaw) = π.individualReachProbability B i*(B.individuals.law i).real (Ioi b) :=
    π.rule.integral_retainedTailReachIndicator π.measurable_rule B.individuals B.intensity π.seedLaw i b
  have hK : (∫ v, K v ∂B.law π.seedLaw) = (B.intensity : Measure ℝ).real (Ioi b)*π.expectedDuration B :=
    π.rule.poisson_compensator_real π.measurable_rule B.individuals B.intensity π.seedLaw measurableSet_Ioi
  simp_rw [hJ,hK] at hR
  have hIndividual : (∑ i, π.individualReachProbability B i*(B.individuals.law i).real (Ioi b)) ≤
      2*π.expectedDuration B*B.individuals.tailCount b := by
    calc
      _ ≤ ∑ i, (2*π.expectedDuration B)*(B.individuals.law i).real (Ioi b) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
          (π.individualReachProbability_le_twice_expectedDuration B i) measureReal_nonneg
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hPoisson : (B.intensity : Measure ℝ).real (Ioi b)*π.expectedDuration B ≤
      2*π.expectedDuration B*(B.intensity : Measure ℝ).real (Ioi b) := by
    nlinarith [mul_nonneg (π.expectedDuration_nonnegative B) (measureReal_nonneg (μ := (B.intensity : Measure ℝ)) (s := Ioi b))]
  have hCount := add_le_add hIndividual hPoisson
  have hScaled := mul_le_mul_of_nonneg_left hCount B.cap.property
  unfold FiniteIntensityHybridInstance.tailCount
  nlinarith [hR,hScaled]

end ProphetSecretary.Limiting
