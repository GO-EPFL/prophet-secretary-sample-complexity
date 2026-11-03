import ProphetSecretary.Probability.FairBitUniform
import ProphetSecretary.Statistics.PlannerRoundedSampler
import ProphetSecretary.Statistics.PlannerSamplerWork

/-!
# Fair-bit seeds for the rounded planner

There are two categorical uniforms and three reservoirs with one uniform per
identity. Componentwise decoding therefore uses exactly `(3n+2)b` bits for a
full seed, and preserves the literal product law of the rounded uniforms.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

def plannerMapSeed {n : ℕ} {α β : Type*} (f : α → β)
    (s : PlannerFieldSeed n α) : PlannerFieldSeed n β :=
  ((f s.1.1, fun i => f (s.1.2 i)), (f s.2.1,
    (fun i => f (s.2.2.1 i), fun i => f (s.2.2.2 i))))

noncomputable def plannerSeedProduct (n : ℕ) {α : Type*} [MeasurableSpace α]
    (μ : Measure α) : Measure (PlannerFieldSeed n α) :=
  let clocks := Measure.pi (fun _ : Fin n => μ)
  (μ.prod clocks).prod (μ.prod (clocks.prod clocks))

instance plannerSeedProduct_probability (n : ℕ) {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] : IsProbabilityMeasure (plannerSeedProduct n μ) := by
  unfold plannerSeedProduct
  infer_instance

lemma measurePreserving_plannerMapSeed (n : ℕ) {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → β} (hf : MeasurePreserving f μ ν) :
    MeasurePreserving (plannerMapSeed (n := n) f) (plannerSeedProduct n μ) (plannerSeedProduct n ν) := by
  have hπ := measurePreserving_pi (fun _ : Fin n => μ) (fun _ => ν) (fun _ => hf)
  exact (hf.prod hπ).prod (hf.prod (hπ.prod hπ))

abbrev PlannerFairSeed (n b : ℕ) := PlannerFieldSeed n (Fin b → Bool)

noncomputable def plannerFairSeedLaw (n b : ℕ) : Measure (PlannerFairSeed n b) :=
  plannerSeedProduct n (fairBitVectorLaw b)

instance plannerFairSeedLaw_probability (n b : ℕ) : IsProbabilityMeasure (plannerFairSeedLaw n b) :=
  inferInstanceAs (IsProbabilityMeasure (plannerSeedProduct n (fairBitVectorLaw b)))

/-- Decode the full transition reservoir with an explicit bit-read count. -/
def countedPlannerFairSeed {n : ℕ} (b : ℕ) (s : PlannerFairSeed n b) : PlannerFieldSeed n ℚ × ℕ :=
  let q := plannerMapSeed (countedDyadicUniform b) s
  (plannerMapSeed Prod.fst q,
    q.1.1.2 + (∑ i : Fin n, (q.1.2 i).2) + q.2.1.2 +
      (∑ i : Fin n, (q.2.2.1 i).2) + ∑ i : Fin n, (q.2.2.2 i).2)

lemma countedPlannerFairSeed_reads {n : ℕ} (b : ℕ) (s : PlannerFairSeed n b) :
    (countedPlannerFairSeed b s).2 = (3*n+2)*b := by
  simp only [countedPlannerFairSeed, plannerMapSeed, countedDyadicUniform_reads,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

noncomputable def plannerFairSeedReal {n : ℕ} (b : ℕ) (s : PlannerFairSeed n b) : PlannerUniformSeed n :=
  plannerMapSeed (fun q : ℚ => (q : ℝ)) (countedPlannerFairSeed b s).1

noncomputable def plannerRoundedSeedLaw (n N : ℕ) (hN : 0 < N) : Measure (PlannerUniformSeed n) :=
  (plannerUniformSeedLaw n).map (plannerRoundSeed N hN)

instance plannerRoundedSeedLaw_probability (n N : ℕ) (hN : 0 < N) :
    IsProbabilityMeasure (plannerRoundedSeedLaw n N hN) :=
  Measure.isProbabilityMeasure_map (measurable_plannerRoundSeed n N hN).aemeasurable

lemma measurePreserving_plannerRoundSeed (n N : ℕ) (hN : 0 < N) :
    MeasurePreserving (plannerRoundSeed (n := n) N hN) (plannerUniformSeedLaw n)
      (plannerRoundedSeedLaw n N hN) := ⟨measurable_plannerRoundSeed n N hN, rfl⟩

lemma plannerRoundedSeedLaw_eq_product (n N : ℕ) (hN : 0 < N) :
    plannerRoundedSeedLaw n N hN =
      plannerSeedProduct n (Instance.uniformClock.map (uniformGridRound N hN)) := by
  let ν := Instance.uniformClock.map (uniformGridRound N hN)
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (measurable_uniformGridRound N hN).aemeasurable
  have hr : MeasurePreserving (uniformGridRound N hN) Instance.uniformClock ν :=
    ⟨measurable_uniformGridRound N hN,rfl⟩
  exact (measurePreserving_plannerMapSeed n hr).map_eq

/-- Actual bounded fair bits have exactly the same joint law as the rounded
continuous planner reservoir. -/
theorem measurePreserving_plannerFairSeedReal (n b : ℕ) :
    MeasurePreserving (plannerFairSeedReal (n := n) b) (plannerFairSeedLaw n b)
      (plannerRoundedSeedLaw n (2^b) (by positivity)) := by
  rw [plannerRoundedSeedLaw_eq_product]
  let ν := Instance.uniformClock.map (uniformGridRound (2^b) (by positivity))
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (measurable_uniformGridRound _ _).aemeasurable
  have hd : MeasurePreserving (fun bits => ((countedDyadicUniform b bits).1 : ℝ)) (fairBitVectorLaw b) ν :=
    ⟨measurable_of_countable _,map_countedDyadicUniform b⟩
  exact measurePreserving_plannerMapSeed n hd

end ProphetSecretary.Statistics
