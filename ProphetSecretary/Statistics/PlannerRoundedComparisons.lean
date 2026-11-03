import ProphetSecretary.Statistics.PlannerUniformSampler
import ProphetSecretary.Probability.DyadicUniformCoupling
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.HasLaw

/-!
# Uniform-grid comparisons in the planner sampler

Categorical choices use finitely many cumulative-probability boundaries.
Bernoulli vector bounds use the actual coordinate marginals of the product
uniform law. Conditional event estimates are obtained by product integration.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

lemma categoricalUniformSample_eq_of_comparisons {n : ℕ} (A : Finset (Fin n))
    (hA : A.Nonempty) (w : Fin n → ℝ) (u v : ℝ)
    (h : ∀ i ∈ A, decide (u < categoricalPrefix A w i) = decide (v < categoricalPrefix A w i)) :
    categoricalUniformSample A hA w u = categoricalUniformSample A hA w v := by
  unfold categoricalUniformSample
  apply Finset.inf'_congr hA rfl
  intro i hi
  have hc : (u < categoricalPrefix A w i) ↔ (v < categoricalPrefix A w i) := by
    exact decide_eq_decide.mp (h i hi)
  by_cases hu : u < categoricalPrefix A w i
  · simp only [if_pos hu, if_pos (hc.mp hu)]
  · simp only [if_neg hu, if_neg (fun hv => hu (hc.mpr hv))]

lemma categoricalUniformSample_rounded_probability {n : ℕ} (A : Finset (Fin n))
    (hA : A.Nonempty) (w : Fin n → ℝ) (N : ℕ) (hN : 0 < N) :
    Instance.uniformClock.real
      {u | categoricalUniformSample A hA w u ≠ categoricalUniformSample A hA w (uniformGridRound N hN u)} ≤
      (A.card : ℝ) / N := by
  let E : Fin n → Set ℝ := fun i =>
    {u | decide (u < categoricalPrefix A w i) ≠ decide (uniformGridRound N hN u < categoricalPrefix A w i)}
  have hsub : {u | categoricalUniformSample A hA w u ≠
      categoricalUniformSample A hA w (uniformGridRound N hN u)} ⊆ ⋃ i ∈ A, E i := by
    intro u hu
    by_contra h
    have hc : ∀ i ∈ A, decide (u < categoricalPrefix A w i) =
        decide (uniformGridRound N hN u < categoricalPrefix A w i) := by
      intro i hi
      by_contra hn
      exact h (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hn⟩⟩)
    exact hu (categoricalUniformSample_eq_of_comparisons A hA w u _ hc)
  calc
    _ ≤ Instance.uniformClock.real (⋃ i ∈ A, E i) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i ∈ A, Instance.uniformClock.real (E i) := measureReal_biUnion_finset_le A E
    _ ≤ ∑ _i ∈ A, 1 / (N : ℝ) := Finset.sum_le_sum (fun i _ =>
      uniformGridRound_strict_comparison_probability N hN (categoricalPrefix A w i))
    _ = _ := by simp [nsmul_eq_mul, div_eq_mul_inv]

lemma rounded_vector_comparison_probability {n : ℕ} (A : Finset (Fin n))
    (r : Fin n → ℝ) (N : ℕ) (hN : 0 < N) :
    (Instance.clocksLaw n).real
      {u | ∃ i ∈ A, decide (u i ≤ r i) ≠ decide (uniformGridRound N hN (u i) ≤ r i)} ≤
      (A.card : ℝ) / N := by
  let E : Fin n → Set (Fin n → ℝ) := fun i =>
    {u | decide (u i ≤ r i) ≠ decide (uniformGridRound N hN (u i) ≤ r i)}
  have hEach (i : Fin n) : (Instance.clocksLaw n).real (E i) ≤ 1 / (N : ℝ) := by
    have hm : MeasurableSet {u : ℝ | decide (u ≤ r i) ≠ decide (uniformGridRound N hN u ≤ r i)} :=
      measurableSet_decide_disagreement _ _
        (measurableSet_le measurable_id measurable_const)
        (measurableSet_le (measurable_uniformGridRound N hN) measurable_const)
    have hp : MeasurePreserving (fun u : Fin n → ℝ => u i) (Instance.clocksLaw n) Instance.uniformClock :=
      measurePreserving_eval (fun _ : Fin n => Instance.uniformClock) i
    have he := hp.hasLaw.measureReal_eq hm
    exact he.le.trans (uniformGridRound_comparison_probability N hN (r i))
  have heq : {u | ∃ i ∈ A, decide (u i ≤ r i) ≠ decide (uniformGridRound N hN (u i) ≤ r i)} =
      ⋃ i ∈ A, E i := by ext u; simp [E]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ A, (Instance.clocksLaw n).real (E i) := measureReal_biUnion_finset_le A E
    _ ≤ ∑ _i ∈ A, 1 / (N : ℝ) := Finset.sum_le_sum (fun i _ => hEach i)
    _ = _ := by simp [nsmul_eq_mul, div_eq_mul_inv]

lemma rounded_vector_moving_comparison_probability {n : ℕ} (A : Finset (Fin n))
    (t t' : ℝ) (N : ℕ) (hN : 0 < N) (ht : |t - t'| ≤ 1 / (N : ℝ)) :
    (Instance.clocksLaw n).real
      {u | ∃ i ∈ A, decide (u i ≤ t) ≠ decide (uniformGridRound N hN (u i) ≤ t')} ≤
      4 * (A.card : ℝ) / N := by
  let E : Fin n → Set (Fin n → ℝ) := fun i =>
    {u | decide (u i ≤ t) ≠ decide (uniformGridRound N hN (u i) ≤ t')}
  have hEach (i : Fin n) : (Instance.clocksLaw n).real (E i) ≤ 4 / (N : ℝ) := by
    have hm : MeasurableSet {u : ℝ | decide (u ≤ t) ≠ decide (uniformGridRound N hN u ≤ t')} :=
      measurableSet_decide_disagreement _ _
        (measurableSet_le measurable_id measurable_const)
        (measurableSet_le (measurable_uniformGridRound N hN) measurable_const)
    have hp : MeasurePreserving (fun u : Fin n → ℝ => u i) (Instance.clocksLaw n) Instance.uniformClock :=
      measurePreserving_eval (fun _ : Fin n => Instance.uniformClock) i
    have he := hp.hasLaw.measureReal_eq hm
    exact he.le.trans (uniformGridRound_moving_comparison_probability N hN t t' ht)
  have heq : {u | ∃ i ∈ A, decide (u i ≤ t) ≠ decide (uniformGridRound N hN (u i) ≤ t')} =
      ⋃ i ∈ A, E i := by ext u; simp [E]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ A, (Instance.clocksLaw n).real (E i) := measureReal_biUnion_finset_le A E
    _ ≤ ∑ _i ∈ A, 4 / (N : ℝ) := Finset.sum_le_sum (fun i _ => hEach i)
    _ = _ := by simp [nsmul_eq_mul, div_eq_mul_inv]; ring

/-- A conditional probability bound is integrated against the actual
independent product law, rather than assumed as a policy interface. -/
lemma product_event_probability_le {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set (Ω × Ξ)) (hE : MeasurableSet E) (c : ℝ)
    (hb : ∀ᵐ x ∂μ, ν.real ((Prod.mk x) ⁻¹' E) ≤ c) : (μ.prod ν).real E ≤ c := by
  let f : Ω × Ξ → ℝ := E.indicator 1
  have hi : Integrable f (μ.prod ν) := (integrable_const 1).indicator hE
  have hf (x : Ω) : (∫ y, f (x, y) ∂ν) = ν.real ((Prod.mk x) ⁻¹' E) := by
    have hs : MeasurableSet ((Prod.mk x) ⁻¹' E) := hE.preimage measurable_prodMk_left
    change (∫ y, (((Prod.mk x) ⁻¹' E).indicator 1) y ∂ν) = _
    exact integral_indicator_one hs
  calc
    _ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
      rw [← integral_indicator_one hE, integral_prod f hi]
    _ ≤ ∫ _x : Ω, c ∂μ := integral_mono_ae hi.integral_prod_left (integrable_const c)
      (hb.mono (fun x hx => (hf x).le.trans hx))
    _ = _ := by simp

end ProphetSecretary.Statistics
