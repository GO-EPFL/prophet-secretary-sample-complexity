import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic

/-!
# Finite superposition of independent Poisson counts

Rates may vanish and the indexing set may be empty. The addition step uses
the library's exact convolution theorem for Poisson laws.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

namespace ProphetSecretary.Probability

lemma poissonMeasure_zero_eq_dirac : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_singleton
  intro m
  cases m <;> simp [poissonMeasure_singleton]

theorem hasLaw_finsetSum_poisson {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℕ} {r : ι → ℝ≥0}
    (hI : iIndepFun X μ) (hX : ∀ i, HasLaw (X i) (poissonMeasure (r i)) μ)
    (s : Finset ι) :
    HasLaw (fun ω => ∑ i ∈ s, X i ω) (poissonMeasure (∑ i ∈ s, r i)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty,poissonMeasure_zero_eq_dirac] using
      (hasLaw_dirac_of_ae_eq (EventuallyEq.rfl : (fun _ : Ω => (0 : ℕ)) =ᵐ[μ] fun _ => 0))
  | @insert i s hi ih =>
    have heq : (∑ j ∈ s, X j) = (fun ω => ∑ j ∈ s, X j ω) := by
      funext ω
      simp only [Finset.sum_apply]
    have ih' : HasLaw (∑ j ∈ s, X j) (poissonMeasure (∑ j ∈ s, r j)) μ := by
      rw [heq]
      exact ih
    have h := (hI.indepFun_finsetSum_of_notMem₀ (fun j => (hX j).aemeasurable) hi).symm.hasLaw_add_poissonMeasure
      (hX i) ih'
    have hadd : (X i + ∑ j ∈ s, X j) = (fun ω => ∑ j ∈ insert i s, X j ω) := by
      funext ω
      simp only [Finset.sum_insert hi,Pi.add_apply,Finset.sum_apply]
    rw [hadd] at h
    simpa only [Finset.sum_insert hi] using h

end ProphetSecretary.Probability
