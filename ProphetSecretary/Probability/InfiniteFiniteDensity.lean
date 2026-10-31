import ProphetSecretary.Probability.InfiniteCoordinateDensity

/-!
# Finitely many likelihood changes in an infinite independent product

All other coordinates retain their original laws. The density is proved by
successive actual coordinate changes, rather than assumed independence of a
policy-specific analytical score.
-/

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace ProphetSecretary.Probability

lemma infinitePi_finite_withDensity {ι A : Type*} [DecidableEq ι] [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (f : ι → A → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, IsProbabilityMeasure ((μ i).withDensity (f i))]
    (s : Finset ι) :
    Measure.infinitePi (fun i => if i ∈ s then (μ i).withDensity (f i) else μ i)=
      (Measure.infinitePi μ).withDensity (fun x => ∏ i ∈ s, f i (x i)) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty,if_false,Finset.prod_empty]
    change (Measure.infinitePi μ)=(Measure.infinitePi μ).withDensity 1
    exact withDensity_one.symm
  | @insert i s hi ih =>
    let ν := fun j => if j ∈ s then (μ j).withDensity (f j) else μ j
    haveI (j : ι) : IsProbabilityMeasure (ν j) := by
      by_cases hj : j ∈ s
      · simpa only [ν,if_pos hj] using (inferInstance : IsProbabilityMeasure ((μ j).withDensity (f j)))
      · simpa only [ν,if_neg hj] using (inferInstance : IsProbabilityMeasure (μ j))
    haveI : IsProbabilityMeasure ((ν i).withDensity (f i)) := by
      simpa only [ν,if_neg hi] using (inferInstance : IsProbabilityMeasure ((μ i).withDensity (f i)))
    have hFamily : (fun j => if j ∈ insert i s then (μ j).withDensity (f j) else μ j)=
        Function.update ν i ((ν i).withDensity (f i)) := by
      funext j
      by_cases hji : j=i
      · subst j
        simp only [Finset.mem_insert_self,if_pos,Function.update_self,ν,if_neg hi]
      · rw [Function.update_of_ne hji]
        by_cases hjs : j ∈ s <;> simp only [Finset.mem_insert,hji,false_or,hjs,if_true,if_false,ν]
    have hProduct : Measurable (fun x : ι → A => ∏ j ∈ s, f j (x j)) :=
      Finset.measurable_fun_prod _ (fun j _ => (hf j).comp (measurable_pi_apply j))
    have hSingle : Measurable (fun x : ι → A => f i (x i)) := (hf i).comp (measurable_pi_apply i)
    rw [hFamily,infinitePi_update_withDensity ν i (f i) (hf i)]
    change ((Measure.infinitePi (fun j => if j ∈ s then (μ j).withDensity (f j) else μ j)).withDensity
      (fun x => f i (x i)))=_
    rw [ih,← withDensity_mul (Measure.infinitePi μ) hProduct hSingle]
    apply congrArg (fun g => (Measure.infinitePi μ).withDensity g)
    funext x
    change (∏ j ∈ s, f j (x j))*f i (x i)=∏ j ∈ insert i s, f j (x j)
    rw [Finset.prod_insert hi]
    exact mul_comm _ _

end ProphetSecretary.Probability
