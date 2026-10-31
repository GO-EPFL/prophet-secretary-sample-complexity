import ProphetSecretary.Limiting.HybridContinuationError
import ProphetSecretary.Limiting.HybridClockMarginal

/-!
# Complete clock-error sums in the augmented hybrid law

The sum ranges over original and anonymous occurrences; ignored virtual zero
identities contribute no action loss. Its count factor is explicit. Clock-law
transport on each analytical Poisson-count branch is proved directly from
independent uniform clock marginals, including zero anonymous intensity.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n q N : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma FiniteIntensityHybridInstance.finiteDesignContinuationError_le
    (B : FiniteIntensityHybridInstance n) (Q : Model.Instance (n+q))
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (u : Fin (n+q+N) → ℝ) (k : Fin (n+N))
    (ht : 0 ≤ u ((HybridZeroSimulation.keepEmbedding n q N).toEmbedding k)) :
    B.finiteDesignContinuationError Q w c u k ≤ Model.optimalScalarValue Q w c+(2*w*(B.cap : ℝ)+c) := by
  let e := (HybridZeroSimulation.keepEmbedding n q N).toEmbedding
  have hD0 := (Q.appendZeros N).continuationAtArrival_nonnegative
    (Q.appendZeros_integrable_maximum N hQ) hw.le hc (fun _ => 0) u (e k)
  have hD1 := (Q.appendZeros N).continuationAtArrival_le_initial
    (Q.appendZeros_integrable_maximum N hQ) hw.le hc (fun _ => 0) u (e k) ht
  rw [Q.optimalScalarValue_appendZeros N hQ hw.le hc] at hD1
  have hA := B.finiteContinuationAtArrival_bounds hw hc (fun _ => 0) (u ∘ e) k ht
  have hAbs : |(Q.appendZeros N).continuationAtArrival w c (fun _ => 0) u (e k)-
      B.finiteContinuationAtArrival w c (fun _ => 0) (u ∘ e) k| ≤
      (Q.appendZeros N).continuationAtArrival w c (fun _ => 0) u (e k)+
        B.finiteContinuationAtArrival w c (fun _ => 0) (u ∘ e) k :=
    abs_le.mpr ⟨by linarith only [hD0],by linarith only [hA.1]⟩
  exact hAbs.trans (add_le_add hD1 hA.2)

noncomputable def FiniteIntensityHybridInstance.clockErrorSum (B : FiniteIntensityHybridInstance n)
    (Q : Model.Instance (n+q)) (w c : ℝ) (v : HybridWorld (n+q) Seed) : ℝ :=
  ∑ k : Fin (n+v.1.1), B.finiteDesignContinuationError Q w c (combinedClocks v.2.2.1 v.1.2) k

omit [MeasurableSpace Seed] in
lemma FiniteIntensityHybridInstance.clockErrorSum_nonnegative (B : FiniteIntensityHybridInstance n)
    (Q : Model.Instance (n+q)) (w c : ℝ) (v : HybridWorld (n+q) Seed) : 0 ≤ B.clockErrorSum Q w c v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma FiniteIntensityHybridInstance.measurable_clockErrorSum (B : FiniteIntensityHybridInstance n)
    (Q : Model.Instance (n+q)) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) : Measurable (B.clockErrorSum (Seed := Seed) Q w c) := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × Model.World (n+q) Seed
  have hu (i : Fin (n+q)) : Measurable (fun v : Ω => v.2.2.1 i) := by fun_prop
  have hv (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  have hClock : Measurable (fun v : Ω => combinedClocks v.2.2.1 v.1) :=
    measurable_pi_lambda _ (fun k => measurable_combinedClocks_family _ hu _ hv k)
  change Measurable (fun v : Ω => ∑ k : Fin (n+N), B.finiteDesignContinuationError Q w c (combinedClocks v.2.2.1 v.1) k)
  apply Finset.measurable_fun_sum
  intro k _
  exact (B.measurable_finiteDesignContinuationError Q hQ hw hc k).comp hClock

lemma FiniteIntensityHybridInstance.integrable_clockErrorSum (B : FiniteIntensityHybridInstance n)
    (Q : Model.Instance (n+q)) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (R : FiniteIntensityHybridInstance (n+q)) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) : Integrable (B.clockErrorSum Q w c) (R.law ν) := by
  have hCount : Integrable (fun v : HybridWorld (n+q) Seed => (v.1.1 : ℝ)) (R.law ν) :=
    (measurePreserving_fst (μ := configurationLaw R.intensity) (ν := R.individuals.worldLaw ν)).integrable_comp_of_integrable
      (configuration_count_integrable R.intensity)
  let K := Model.optimalScalarValue Q w c+(2*w*(B.cap : ℝ)+c)
  have hDom : Integrable (fun v : HybridWorld (n+q) Seed => ((n : ℝ)+(v.1.1 : ℝ))*K) (R.law ν) :=
    ((integrable_const (n : ℝ)).add hCount).mul_const K
  apply hDom.mono' (B.measurable_clockErrorSum Q hQ hw hc).aestronglyMeasurable
  filter_upwards [hybrid_combined_clocks_regular R.individuals R.intensity ν] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg (B.clockErrorSum_nonnegative Q w c v)]
  unfold FiniteIntensityHybridInstance.clockErrorSum
  calc
    _ ≤ ∑ _k : Fin (n+v.1.1), K := Finset.sum_le_sum fun k _ =>
      B.finiteDesignContinuationError_le Q hQ hw hc _ k
        (hv.2 ((HybridZeroSimulation.keepEmbedding n q v.1.1).toEmbedding k)).1.le
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add]

lemma clockErrorBranch_measurePreserving (P : Model.Instance (n+q)) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (N : ℕ) :
    MeasurePreserving (fun v : (Fin N → Point) × Model.World (n+q) Seed => combinedClocks v.2.2.1 v.1)
      ((arrayLaw μ N).prod (P.worldLaw ν)) (Model.Instance.clocksLaw (n+q+N)) := by
  have h0 := (array_times_measurePreserving μ N).prod (P.world_clocks_measurePreserving ν)
  have h1 := (Measure.measurePreserving_swap (μ := Model.Instance.clocksLaw N) (ν := Model.Instance.clocksLaw (n+q))).comp h0
  exact (Model.Instance.appendClocks_measurePreserving (n+q) N).comp h1

lemma FiniteIntensityHybridInstance.hasSum_clockErrorSum_branches
    (B : FiniteIntensityHybridInstance n) (Q : Model.Instance (n+q))
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (R : FiniteIntensityHybridInstance (n+q))
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    HasSum (fun N : ℕ => poissonWeight R.intensity.mass N*
      (∫ u : Fin (n+q+N) → ℝ, ∑ k : Fin (n+N), B.finiteDesignContinuationError Q w c u k
        ∂Model.Instance.clocksLaw (n+q+N)))
      (∫ v, B.clockErrorSum Q w c v ∂R.law ν) := by
  have hMeas := B.measurable_clockErrorSum (Seed := Seed) Q hQ hw hc
  have hInt := B.integrable_clockErrorSum Q hQ R ν hw hc
  have hMix := hasSum_worldLaw_fibers R.intensity (R.individuals.worldLaw ν) _ hMeas hInt
  have he (N : ℕ) : (∫ v, B.clockErrorSum Q w c (configurationMk N v.1,v.2)
        ∂(arrayLaw R.intensity N).prod (R.individuals.worldLaw ν)) =
      (∫ u : Fin (n+q+N) → ℝ, ∑ k : Fin (n+N), B.finiteDesignContinuationError Q w c u k
        ∂Model.Instance.clocksLaw (n+q+N)) := by
    have hMP := clockErrorBranch_measurePreserving R.individuals R.intensity ν N
    have hf : Measurable (fun u : Fin (n+q+N) → ℝ => ∑ k : Fin (n+N), B.finiteDesignContinuationError Q w c u k) :=
      Finset.measurable_fun_sum _ (fun k _ => B.measurable_finiteDesignContinuationError Q hQ hw hc k)
    exact hMP.hasLaw.integral_comp hf.aestronglyMeasurable
  convert hMix using 1
  · funext N
    rw [he N]
  · rfl

end ProphetSecretary.Limiting
