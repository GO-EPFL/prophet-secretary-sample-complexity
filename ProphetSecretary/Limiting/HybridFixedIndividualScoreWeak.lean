import ProphetSecretary.Limiting.HybridFixedCanonicalWeak
import ProphetSecretary.Probability.CenteredBoundedScore

/-!
# Individual-score weighted evaluation of a fixed canonical callback

A fixed bounded continuous individual observable is centered under each
actual evaluation marginal. Its scale is fixed across the sequence. The
complete individual's value is analytical score data even if it arrives
after selection; the callback receives no additional observations.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

theorem FiniteIntensityHybridInstance.fixed_valueRule_individual_observables_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ps : ℕ → Model.Instance n) (P : Model.Instance n)
    (hP : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) atTop (𝓝 (P.marginalProbabilityLaw i)))
    {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ} (hμ : Tendsto μs atTop (𝓝 μ))
    (i : Fin n) (f : ℝ →ᵇ ℝ) (Φ : ((ℝ × ℝ) × Model.World n Unit) →ᵇ ℝ) :
    Tendsto (fun m => ∫ q, centeredBoundedScore ((Ps m).law i) f (q.2.1 i)*
        Φ (((B.valueRule w c).realizedReward 0 q,(B.valueRule w c).realizedDuration q),q.2)
      ∂hybridWorldLaw (Ps m) (μs m) (Measure.dirac ())) atTop
      (𝓝 (∫ q, centeredBoundedScore (P.law i) f (q.2.1 i)*
        Φ (((B.valueRule w c).realizedReward 0 q,(B.valueRule w c).realizedDuration q),q.2)
        ∂hybridWorldLaw P μ (Measure.dirac ()))) := by
  let F : HybridWorld n Unit → ℝ := fun q => Φ (((B.valueRule w c).realizedReward 0 q,
    (B.valueRule w c).realizedDuration q),q.2)
  let g : ((ℝ × ℝ) × Model.World n Unit) →ᵇ ℝ :=
    f.compContinuous ⟨(fun z => z.2.1 i),by fun_prop⟩
  have hBase := B.fixed_valueRule_observables_tendsto ha hw hc Ps P hP hμ Φ
  have hProduct : Tendsto (fun m => ∫ q, f (q.2.1 i)*F q
      ∂hybridWorldLaw (Ps m) (μs m) (Measure.dirac ())) atTop
      (𝓝 (∫ q, f (q.2.1 i)*F q ∂hybridWorldLaw P μ (Measure.dirac ()))) := by
    simpa only [g,BoundedContinuousFunction.coe_mul,Pi.mul_apply,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,F] using
      B.fixed_valueRule_observables_tendsto ha hw hc Ps P hP hμ (g*Φ)
  have hMean := centeredScore_mean_tendsto (hP i) f
  have hRule := B.valueRule_isMeasurable hw.le hc.le
  have hF : Measurable F := Φ.continuous.measurable.comp
    ((((B.valueRule w c).measurable_realizedReward hRule 0).prodMk
      ((B.valueRule w c).measurable_realizedDuration hRule)).prodMk measurable_snd)
  have hXi : Measurable (fun q : HybridWorld n Unit => q.2.1 i) := by fun_prop
  have hInt (Q : Model.Instance n) (η : FiniteMeasure ℝ) : Integrable F (hybridWorldLaw Q η (Measure.dirac ())) :=
    Integrable.of_bound hF.aestronglyMeasurable ‖Φ‖ (Eventually.of_forall (fun q =>
      Φ.norm_coe_le_norm (((B.valueRule w c).realizedReward 0 q,(B.valueRule w c).realizedDuration q),q.2)))
  have hProductInt (Q : Model.Instance n) (η : FiniteMeasure ℝ) :
      Integrable (fun q => f (q.2.1 i)*F q) (hybridWorldLaw Q η (Measure.dirac ())) := by
    apply Integrable.of_bound ((f.continuous.measurable.comp hXi).mul hF).aestronglyMeasurable (‖f‖*‖Φ‖)
    exact Eventually.of_forall (fun q => by
      change ‖f (q.2.1 i)*F q‖≤‖f‖*‖Φ‖
      rw [norm_mul]
      exact mul_le_mul (f.norm_coe_le_norm (q.2.1 i))
        (Φ.norm_coe_le_norm (((B.valueRule w c).realizedReward 0 q,(B.valueRule w c).realizedDuration q),q.2))
        (norm_nonneg _) (norm_nonneg f))
  have hEq (Q : Model.Instance n) (η : FiniteMeasure ℝ) :
      (∫ q, centeredBoundedScore (Q.law i) f (q.2.1 i)*F q ∂hybridWorldLaw Q η (Measure.dirac ())) =
      ((∫ q, f (q.2.1 i)*F q ∂hybridWorldLaw Q η (Measure.dirac ()))-
        (∫ x, f x ∂Q.law i)*(∫ q, F q ∂hybridWorldLaw Q η (Measure.dirac ())))/boundedScoreScale f := by
    have he : (fun q : HybridWorld n Unit => centeredBoundedScore (Q.law i) f (q.2.1 i)*F q) =
        (fun q => (f (q.2.1 i)*F q-(∫ x, f x ∂Q.law i)*F q)/boundedScoreScale f) := by
      funext q
      unfold centeredBoundedScore centeredRangeScore
      ring
    rw [he,integral_div,integral_sub (hProductInt Q η) ((hInt Q η).const_mul _),integral_const_mul]
  have hLimit := (hProduct.sub (hMean.mul hBase)).div_const (boundedScoreScale f)
  change Tendsto (fun m => ∫ q, centeredBoundedScore ((Ps m).law i) f (q.2.1 i)*F q
      ∂hybridWorldLaw (Ps m) (μs m) (Measure.dirac ())) atTop
      (𝓝 (∫ q, centeredBoundedScore (P.law i) f (q.2.1 i)*F q ∂hybridWorldLaw P μ (Measure.dirac ())))
  simp_rw [hEq]
  exact hLimit
end ProphetSecretary.Limiting
