import ProphetSecretary.Statistics.FinitePriorSwap
import ProphetSecretary.Probability.ConditionalPullback
import ProphetSecretary.Probability.ConditionalTesting

/-!
# The hypothetical posterior is an actual conditional projection

The next training posterior is pulled back by the constructed ONLINE/unused-round
swap. Conditional expectation uniqueness identifies its actual observation sigma
algebra. This variable is analytical and is not supplied to the training protocol.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ}

abbrev hypotheticalSigma (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) : MeasurableSpace (BaseWorld F N) :=
  (F.dataSigma N b (k+1)).comap (F.swapBaseEquiv N (nextColumn N b k hk))

lemma hypotheticalSigma_le (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) :
    F.hypotheticalSigma N b k hk≤(inferInstance : MeasurableSpace (BaseWorld F N)) :=
  (MeasurableSpace.comap_mono (F.dataSigma_le N b (k+1))).trans (F.swapBaseEquiv N (nextColumn N b k hk)).measurable.comap_le

lemma rewardIndicator_integrable (F : FinitePrior n) (N : ℕ) :
    Integrable (F.rewardIndicator (N:=N)) (F.law N) := by
  apply Integrable.of_bound (F.measurable_rewardIndicator N).aestronglyMeasurable 1
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (F.rewardIndicator_mem_unit ω).1]
    exact (F.rewardIndicator_mem_unit ω).2

lemma hypotheticalPosterior_stronglyMeasurable (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) :
    StronglyMeasurable[F.hypotheticalSigma N b k hk] (F.hypotheticalPosterior N b k hk) := by
  have hm : @Measurable (BaseWorld F N) (BaseWorld F N) (F.hypotheticalSigma N b k hk)
      (F.dataSigma N b (k+1)) (F.swapBaseEquiv N (nextColumn N b k hk)) := Measurable.of_comap_le le_rfl
  exact (F.posterior_stronglyMeasurable N b (k+1)).comp_measurable hm

/-- The conditional projection is proved from the actual swap, not asserted as a
property of an abstract posterior interface. -/
theorem hypotheticalPosterior_eq_condExp (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) :
    F.hypotheticalPosterior N b k hk =ᵐ[F.law N]
      (F.law N)[F.rewardIndicator|F.hypotheticalSigma N b k hk] := by
  have h := ProphetSecretary.Probability.condExp_comp_measurePreserving (F.law N)
    (F.swapBaseEquiv_measurePreserving N (nextColumn N b k hk)) (F.dataSigma_le N b (k+1))
    (F.rewardIndicator_integrable N)
  change (fun ω => (F.law N)[F.rewardIndicator|F.dataSigma N b (k+1)]
    (F.swapBaseEquiv N (nextColumn N b k hk) ω)) =ᵐ[F.law N]
      (F.law N)[F.rewardIndicator|(F.dataSigma N b (k+1)).comap
        (F.swapBaseEquiv N (nextColumn N b k hk))]
  simpa only [rewardIndicator_swap] using h

theorem hypotheticalPosterior_testing (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N)
    {H : BaseWorld F N → ℝ} (hH : StronglyMeasurable[F.hypotheticalSigma N b k hk] H)
    (hProd : Integrable (H*F.rewardIndicator) (F.law N)) :
    (∫ ω, H ω*F.rewardIndicator ω ∂F.law N)=
      ∫ ω, H ω*F.hypotheticalPosterior N b k hk ω ∂F.law N := by
  have h := ProphetSecretary.Probability.integral_observed_mul_condExp (F.law N)
    (F.hypotheticalSigma_le N b k hk) hH (F.rewardIndicator_integrable N) hProd
  exact h.trans (integral_congr_ae ((F.hypotheticalPosterior_eq_condExp N b k hk).symm.mono
    fun ω hω => congrArg (H ω*·) hω))

end ProphetSecretary.Statistics.FinitePrior
