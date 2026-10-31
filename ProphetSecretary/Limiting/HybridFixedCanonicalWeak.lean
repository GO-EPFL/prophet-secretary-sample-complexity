import ProphetSecretary.Limiting.HybridValueBranchPayoff
import ProphetSecretary.Limiting.HybridRetainedWorldWeak
import ProphetSecretary.Limiting.PoissonObservableConvergence

/-!
# Weak evaluation continuity of a fixed canonical hybrid policy

The design and both scalar weights are fixed before evaluation laws vary.
Joint bounded continuous observables of reward, elapsed duration and retained
data converge under the actual independent laws. This does not reoptimize a
policy after changing its evaluation distribution.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

/-- Fixed-callback joint outcome convergence, including zero limiting
anonymous intensity and arbitrary atoms in retained offer distributions. -/
theorem FiniteIntensityHybridInstance.fixed_valueRule_observables_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ps : ℕ → Model.Instance n) (P : Model.Instance n)
    (hP : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) atTop (𝓝 (P.marginalProbabilityLaw i)))
    {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ} (hμ : Tendsto μs atTop (𝓝 μ))
    (Φ : ((ℝ × ℝ) × Model.World n Unit) →ᵇ ℝ) :
    Tendsto (fun m => ∫ q, Φ (((B.valueRule w c).realizedReward 0 q,
        (B.valueRule w c).realizedDuration q),q.2)
      ∂hybridWorldLaw (Ps m) (μs m) (Measure.dirac ())) atTop
      (𝓝 (∫ q, Φ (((B.valueRule w c).realizedReward 0 q,
        (B.valueRule w c).realizedDuration q),q.2)
        ∂hybridWorldLaw P μ (Measure.dirac ()))) := by
  let F : HybridWorld n Unit → ℝ := fun q => Φ (((B.valueRule w c).realizedReward 0 q,
    (B.valueRule w c).realizedDuration q),q.2)
  have hRule := B.valueRule_isMeasurable hw.le hc.le
  have hF : Measurable F := Φ.continuous.measurable.comp
    ((((B.valueRule w c).measurable_realizedReward hRule 0).prodMk
      ((B.valueRule w c).measurable_realizedDuration hRule)).prodMk measurable_snd)
  have hBound (q : HybridWorld n Unit) : |F q|≤‖Φ‖*((q.1.1:ℝ)+1) := by
    have hb : |F q|≤‖Φ‖ := by simpa only [Real.norm_eq_abs] using (Φ.norm_coe_le_norm
      (((B.valueRule w c).realizedReward 0 q,(B.valueRule w c).realizedDuration q),q.2))
    exact hb.trans (le_mul_of_one_le_right (norm_nonneg Φ) (by have := Nat.cast_nonneg (α := ℝ) q.1.1; linarith))
  have hCont (N : ℕ) : ∀ᵐ q ∂(arrayLaw μ N).prod (P.worldLaw (Measure.dirac ())),
      ContinuousAt (fun q : (Fin N → Point) × Model.World n Unit => F (configurationMk N q.1,q.2)) q := by
    filter_upwards [B.valueRule_branch_payoffs_continuousAt_ae ha hw hc P μ N] with q hq
    exact Φ.continuous.continuousAt.comp (x := q) ((hq.1.prodMk hq.2).prodMk continuous_snd.continuousAt)
  exact poissonObservable_integral_tendsto hμ (retainedWorldProbabilityLaw_tendsto Ps P hP)
    F hF (norm_nonneg Φ) hBound hCont
end ProphetSecretary.Limiting
