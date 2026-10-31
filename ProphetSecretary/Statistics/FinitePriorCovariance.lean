import ProphetSecretary.Statistics.FinitePriorHypothetical
import ProphetSecretary.Statistics.EmpiricalMomentAbsorption

/-!
# Target covariance from an actual unused-round swap

The posterior increment on the right is that of the real training filtration.
The hypothetical online observation is used solely in conditional projection;
its squared movement has the same expectation by the constructed swap.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ}

lemma hypotheticalPosterior_mem_unit (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) :
    ∀ᵐ ω ∂F.law N, F.hypotheticalPosterior N b k hk ω∈Icc (0:ℝ) 1 :=
  (F.swapBaseEquiv_measurePreserving N (nextColumn N b k hk)).quasiMeasurePreserving.ae
    (F.posterior_mem_unit N b (k+1))

lemma posterior_measurable (F : FinitePrior n) (N b k : ℕ) : Measurable (F.posterior N b k) :=
  ((F.posterior_stronglyMeasurable N b k).mono (F.dataSigma_le N b k)).measurable

lemma hypotheticalPosterior_measurable (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) :
    Measurable (F.hypotheticalPosterior N b k hk) :=
  ((F.hypotheticalPosterior_stronglyMeasurable N b k hk).mono (F.hypotheticalSigma_le N b k hk)).measurable

lemma unit_abs_sub_le_one {x y : ℝ} (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) : |x-y|≤1 :=
  abs_le.mpr ⟨by linarith only [hx.1,hy.2],by linarith only [hx.2,hy.1]⟩

/-- Source covariance step in `eq:bayes-target-score`, before adding an independent
policy seed. Its observable factor may depend on the complete ONLINE vector. -/
theorem target_covariance_le (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N)
    {H : BaseWorld F N → ℝ} (hH : StronglyMeasurable[F.hypotheticalSigma N b k hk] H)
    (hHB : ∀ᵐ ω ∂F.law N, |H ω|≤1) :
    |∫ ω, (F.rewardIndicator ω-F.posterior N b k ω)*H ω ∂F.law N|≤
      Real.sqrt (∫ ω, (F.posterior N b (k+1) ω-F.posterior N b k ω)^2 ∂F.law N) := by
  let μ := F.law N
  let Q := F.rewardIndicator (N:=N)
  let L := F.posterior N b k
  let U := F.hypotheticalPosterior N b k hk
  have hHm := (hH.mono (F.hypotheticalSigma_le N b k hk)).measurable
  have hHI : Integrable H μ := Integrable.of_bound hHm.aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hHB)
  have hQB : ∀ᵐ ω ∂μ, ‖Q ω‖≤1 := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (F.rewardIndicator_mem_unit ω).1]
    exact (F.rewardIndicator_mem_unit ω).2
  have hLB : ∀ᵐ ω ∂μ, ‖L ω‖≤1 := (F.posterior_mem_unit N b k).mono fun ω hω => by
    rw [Real.norm_eq_abs,abs_of_nonneg hω.1]
    exact hω.2
  have hUB : ∀ᵐ ω ∂μ, ‖U ω‖≤1 := (F.hypotheticalPosterior_mem_unit N b k hk).mono fun ω hω => by
    rw [Real.norm_eq_abs,abs_of_nonneg hω.1]
    exact hω.2
  have hQH : Integrable (fun ω => Q ω*H ω) μ := hHI.bdd_mul (F.measurable_rewardIndicator N).aestronglyMeasurable hQB
  have hLH : Integrable (fun ω => L ω*H ω) μ := hHI.bdd_mul (F.posterior_measurable N b k).aestronglyMeasurable hLB
  have hUH : Integrable (fun ω => U ω*H ω) μ := hHI.bdd_mul (F.hypotheticalPosterior_measurable N b k hk).aestronglyMeasurable hUB
  have hTest : (∫ ω, Q ω*H ω ∂μ)=∫ ω, U ω*H ω ∂μ := by
    have h := F.hypotheticalPosterior_testing N b k hk hH (by
      change Integrable (fun ω => H ω*F.rewardIndicator ω) (F.law N)
      simpa only [Q,μ,mul_comm] using hQH)
    simpa only [μ,Q,U,mul_comm] using h
  have hDiff : (∫ ω, (Q ω-L ω)*H ω ∂μ)=∫ ω, (U ω-L ω)*H ω ∂μ := by
    simp_rw [sub_mul]
    rw [integral_sub hQH hLH,integral_sub hUH hLH,hTest]
  have hDB : ∀ᵐ ω ∂μ, |U ω-L ω|≤1 := by
    filter_upwards [F.hypotheticalPosterior_mem_unit N b k hk,F.posterior_mem_unit N b k] with ω hU hL
    exact unit_abs_sub_le_one hU hL
  have hDI : Integrable (fun ω => |U ω-L ω|) μ := Integrable.of_bound
    (by simpa only [Real.norm_eq_abs,Pi.sub_apply,U,L] using ((F.hypotheticalPosterior_measurable N b k hk).sub (F.posterior_measurable N b k)).norm.aestronglyMeasurable) 1
    (by simpa only [Real.norm_eq_abs,abs_abs] using hDB)
  have hD2 : Integrable (fun ω => |U ω-L ω|^2) μ := Integrable.of_bound
    (by simpa only [Real.norm_eq_abs,Pi.sub_apply,U,L] using (((F.hypotheticalPosterior_measurable N b k hk).sub (F.posterior_measurable N b k)).norm.pow_const 2).aestronglyMeasurable) 1 (by
      filter_upwards [hDB] with ω hω
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (abs_nonneg _) hω)
  change |∫ ω, (Q ω-L ω)*H ω ∂μ|≤_
  rw [hDiff,←F.hypothetical_increment_energy N b k hk]
  calc
    |∫ ω, (U ω-L ω)*H ω ∂μ|≤∫ ω, |(U ω-L ω)*H ω| ∂μ := abs_integral_le_integral_abs
    _≤∫ ω, |U ω-L ω| ∂μ := integral_mono_ae (by simpa only [Pi.sub_apply,←sub_mul] using (hUH.sub hLH).abs) hDI (by
      filter_upwards [hHB] with ω hω
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hω)
    _≤Real.sqrt (∫ ω, |U ω-L ω|^2 ∂μ) := ProphetSecretary.Statistics.integral_le_sqrt_second μ hDI hD2
    _=Real.sqrt (∫ ω, (U ω-L ω)^2 ∂μ) := by simp only [sq_abs]

end ProphetSecretary.Statistics.FinitePrior
