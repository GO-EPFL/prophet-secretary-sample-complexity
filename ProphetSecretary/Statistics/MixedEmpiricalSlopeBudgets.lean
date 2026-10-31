import ProphetSecretary.Statistics.MixedEmpiricalSlopePremium

/-!
# Mixed scalar-increment predictable budgets

The actual conditional second and sixth moments sum to the normalizations
U_b/k and E[U_b]/k^5. Known marginal jumps are exactly zero, while the
nonnegative true premium budget may include every marginal.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma integrable_mixedTrueSlopePremiumSum_fixed_pow (P : Instance n) (known : Finset (Fin n))
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z')
    (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (r : ℕ) :
    Integrable (fun a : (Fin n × Fin k) → ℝ => mixedTrueSlopePremiumSum P known z z' u a ^ r)
      (P.trainingCoordinateLaw k) :=
  integrable_mixedTrueSlopePremiumSum_pow P hP known hz hzz (P.trainingCoordinateLaw k)
    (a := id) (u := fun _ => u) (fun q => measurable_pi_apply q) (fun _ => measurable_const)
    (Filter.Eventually.of_forall (fun _ => hu)) r

theorem mixedSlopeReverseProcess_quadraticVariation_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (horder : Instance.HasArrivalOrder u p) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      ProphetSecretary.Probability.predictableQuadraticVariation (reverseTrainingFiltration p)
        (P.trainingCoordinateLaw k) (mixedSlopeReverseProcess P known p z z' u) (n * k) a ≤
        mixedTrueSlopePremiumSum P known z z' u a / k := by
  simpa only [ProphetSecretary.Probability.predictableQuadraticVariation, pow_one] using
    mixedSlopeReverseProcess_conditional_budget_sum P known hbound p hz hzz u hu horder 1 (Or.inl rfl)

theorem mixedSlopeReverseProcess_sixth_jump_budget (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (horder : Instance.HasArrivalOrder u p) :
    (∑ m ∈ Finset.range (n * k), ∫ a,
      (mixedSlopeReverseProcess P known p z z' u (m + 1) a - mixedSlopeReverseProcess P known p z z' u m a) ^ 6
        ∂P.trainingCoordinateLaw k) ≤
      (∫ a, mixedTrueSlopePremiumSum P known z z' u a ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 5 := by
  have hLI : Integrable (fun a => ∑ m ∈ Finset.range (n * k),
      ((P.trainingCoordinateLaw k)[(fun a =>
        (mixedSlopeReverseProcess P known p z z' u (m + 1) a - mixedSlopeReverseProcess P known p z z' u m a) ^ 6) |
        reverseTrainingFiltration p m]) a) (P.trainingCoordinateLaw k) :=
    integrable_finsetSum _ (fun _ _ => integrable_condExp)
  have hUI : Integrable (fun a : (Fin n × Fin k) → ℝ => mixedTrueSlopePremiumSum P known z z' u a)
      (P.trainingCoordinateLaw k) := by
    simpa only [pow_one] using integrable_mixedTrueSlopePremiumSum_fixed_pow (k := k) P known
      (P.integrable_maximum_of_bounded hbound) hz hzz u hu 1
  have hineq := integral_mono_ae hLI (hUI.div_const ((k : ℝ) ^ 5))
    (mixedSlopeReverseProcess_conditional_budget_sum P known hbound p hz hzz u hu horder 5 (Or.inr rfl))
  have hMean : (∫ a, ∑ m ∈ Finset.range (n * k),
      ((P.trainingCoordinateLaw k)[(fun a =>
        (mixedSlopeReverseProcess P known p z z' u (m + 1) a - mixedSlopeReverseProcess P known p z z' u m a) ^ 6) |
        reverseTrainingFiltration p m]) a ∂P.trainingCoordinateLaw k) =
      ∑ m ∈ Finset.range (n * k), ∫ a,
        (mixedSlopeReverseProcess P known p z z' u (m + 1) a - mixedSlopeReverseProcess P known p z z' u m a) ^ 6
          ∂P.trainingCoordinateLaw k := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl (fun m _ => integral_condExp ((reverseTrainingFiltration (k := k) p).le m))
    · intro m _
      exact integrable_condExp
  rw [hMean, integral_div] at hineq
  exact hineq

end ProphetSecretary.Model
