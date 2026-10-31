import ProphetSecretary.Statistics.FinitePriorOnlineObservation
import ProphetSecretary.Statistics.FinitePriorCovariance
import ProphetSecretary.Probability.ConditionalProductLift

/-!
# Independent policy randomness in the finite-prior covariance experiment

The auxiliary law is a common independent product factor. It may contain the
uniform arrival clocks and an arbitrary measurable policy seed. Training-only
conditioning leaves the actual posterior unchanged. A measurable online payoff
may use the current training data, complete online vector (analytically), and
auxiliary randomness; its target covariance costs precisely the square root of
the next actual training posterior's mean squared movement.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ} {Aux : Type*} [MeasurableSpace Aux]

noncomputable abbrev auxiliaryWorldLaw (F : FinitePrior n) (N : ℕ) (ν : Measure Aux) := (F.law N).prod ν

lemma posterior_with_independent_aux (F : FinitePrior n) (N b k : ℕ)
    (ν : Measure Aux) [IsProbabilityMeasure ν] :
    (fun w : BaseWorld F N × Aux => F.posterior N b k w.1) =ᵐ[F.auxiliaryWorldLaw N ν]
      (F.auxiliaryWorldLaw N ν)[(fun w => F.rewardIndicator w.1)|(F.dataSigma N b k).comap Prod.fst] := by
  exact ProphetSecretary.Probability.condExp_prod_lift (F.law N) ν (F.dataSigma_le N b k) (F.rewardIndicator_integrable N)

/-- The genuine observation available to an online execution, with independent
clock/seed randomness adjoined. It never contains an unused training column. -/
def onlinePayoff (F : FinitePrior n) (N b k : ℕ)
    (γ : (ValueArray n N × (Fin n → ℝ)) × Aux → ℝ) (w : BaseWorld F N × Aux) : ℝ :=
  γ ((F.observe N b k w.1,F.onlineValues w.1),w.2)

lemma measurable_onlinePayoff (F : FinitePrior n) (N b k : ℕ)
    {γ : (ValueArray n N × (Fin n → ℝ)) × Aux → ℝ} (hγ : Measurable γ) :
    Measurable (F.onlinePayoff N b k γ) :=
  hγ.comp (((F.measurable_observe N b k).comp measurable_fst).prodMk
    ((F.measurable_onlineValues N).comp measurable_fst) |>.prodMk measurable_snd)

/-- Covariance statement used in `eq:bayes-target-score`, with arbitrary independent
policy randomness. The right side is the actual training filtration increment. -/
theorem target_covariance_with_aux_le (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N)
    (ν : Measure Aux) [IsProbabilityMeasure ν]
    {γ : (ValueArray n N × (Fin n → ℝ)) × Aux → ℝ} (hγ : Measurable γ)
    (hΓ : ∀ᵐ w ∂F.auxiliaryWorldLaw N ν, |F.onlinePayoff N b k γ w|≤1) :
    |∫ w, (F.rewardIndicator w.1-F.posterior N b k w.1)*F.onlinePayoff N b k γ w
      ∂F.auxiliaryWorldLaw N ν|≤
      Real.sqrt (∫ ω, (F.posterior N b (k+1) ω-F.posterior N b k ω)^2 ∂F.law N) := by
  let μ := F.law N
  let Γ := F.onlinePayoff N b k γ
  let H : BaseWorld F N → ℝ := fun ω => ∫ a, Γ (ω,a) ∂ν
  have hΓm := F.measurable_onlinePayoff N b k hγ
  have hPair : @Measurable (BaseWorld F N) (ValueArray n N × (Fin n → ℝ))
      (F.hypotheticalSigma N b k hk) _ (fun ω => (F.observe N b k ω,F.onlineValues ω)) := by
    rw [F.hypotheticalSigma_eq_onlineObservationSigma N b k hk]
    exact Measurable.of_comap_le le_rfl
  have hH : StronglyMeasurable[F.hypotheticalSigma N b k hk] H :=
    (hγ.stronglyMeasurable.integral_prod_right').comp_measurable hPair
  have hHB : ∀ᵐ ω ∂μ, |H ω|≤1 := by
    have hSec := Measure.ae_ae_of_ae_prod hΓ
    filter_upwards [hSec] with ω hω
    simpa only [H,Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=ν) (f:=fun a => Γ (ω,a))
        (by simpa only [Real.norm_eq_abs] using hω)
  have hDiffB : ∀ᵐ w ∂μ.prod ν, |F.rewardIndicator w.1-F.posterior N b k w.1|≤1 :=
    (measurePreserving_fst (μ:=μ) (ν:=ν)).quasiMeasurePreserving.ae (by
      filter_upwards [F.posterior_mem_unit N b k] with ω hω
      exact unit_abs_sub_le_one (F.rewardIndicator_mem_unit ω) hω)
  have hInt : Integrable (fun w : BaseWorld F N × Aux =>
      (F.rewardIndicator w.1-F.posterior N b k w.1)*Γ w) (μ.prod ν) := by
    apply Integrable.of_bound
      ((((F.measurable_rewardIndicator N).comp measurable_fst).sub
        ((F.posterior_measurable N b k).comp measurable_fst)).mul hΓm).aestronglyMeasurable 1
    filter_upwards [hDiffB,hΓ] with w hD hG
    change ‖(F.rewardIndicator w.1-F.posterior N b k w.1)*Γ w‖≤1
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_one₀ hD (abs_nonneg _) hG
  have hFub : (∫ w : BaseWorld F N × Aux,
      (F.rewardIndicator w.1-F.posterior N b k w.1)*Γ w ∂μ.prod ν)=
      ∫ ω, (F.rewardIndicator ω-F.posterior N b k ω)*H ω ∂μ := by
    rw [integral_prod _ hInt]
    simp only [H,integral_const_mul]
  change |∫ w : BaseWorld F N × Aux,
    (F.rewardIndicator w.1-F.posterior N b k w.1)*Γ w ∂μ.prod ν|≤_
  rw [hFub]
  exact F.target_covariance_le N b k hk hH hHB

end ProphetSecretary.Statistics.FinitePrior
