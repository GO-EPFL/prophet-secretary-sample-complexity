import ProphetSecretary.Limiting.HybridFixedBandScoreWeak
import ProphetSecretary.Probability.WeakFiniteUpperTail

/-!
# Centered Poisson band-score transfer for a fixed canonical callback

Each complete band count is centered by its own actual intensity mass.
The center converges at a continuity boundary; the policy design and scalar
weights remain fixed while the evaluation laws vary.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical NNReal
namespace ProphetSecretary.Limiting
variable {n : ℕ}

theorem FiniteIntensityHybridInstance.fixed_valueRule_centeredBand_observables_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ps : ℕ → Model.Instance n) (P : Model.Instance n)
    (hP : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) atTop (𝓝 (P.marginalProbabilityLaw i)))
    {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ} (hμ : Tendsto μs atTop (𝓝 μ))
    (b : ℝ) (hAtom : (μ:Measure ℝ) {b}=0) (Φ : ((ℝ × ℝ) × Model.World n Unit) →ᵇ ℝ) :
    Tendsto (fun m => ∫ q, ((pointCount (univ ×ˢ Ioi b) q.1:ℝ)-(μs m:Measure ℝ).real (Ioi b))*
        Φ (((B.valueRule w c).realizedReward 0 q,(B.valueRule w c).realizedDuration q),q.2)
      ∂hybridWorldLaw (Ps m) (μs m) (Measure.dirac ())) atTop
      (𝓝 (∫ q, ((pointCount (univ ×ˢ Ioi b) q.1:ℝ)-(μ:Measure ℝ).real (Ioi b))*
        Φ (((B.valueRule w c).realizedReward 0 q,(B.valueRule w c).realizedDuration q),q.2)
        ∂hybridWorldLaw P μ (Measure.dirac ()))) := by
  let F : HybridWorld n Unit → ℝ := fun q => Φ (((B.valueRule w c).realizedReward 0 q,
    (B.valueRule w c).realizedDuration q),q.2)
  let C : HybridWorld n Unit → ℝ := fun q => (pointCount (univ ×ˢ Ioi b) q.1:ℝ)
  have hBase := B.fixed_valueRule_observables_tendsto ha hw hc Ps P hP hμ Φ
  have hBand : Tendsto (fun m => ∫ q, C q*F q ∂hybridWorldLaw (Ps m) (μs m) (Measure.dirac ())) atTop
      (𝓝 (∫ q, C q*F q ∂hybridWorldLaw P μ (Measure.dirac ()))) := by
    simpa only [sub_zero,C,F] using B.fixed_valueRule_band_observables_tendsto ha hw hc Ps P hP hμ b 0 hAtom Φ
  have hMass := ProphetSecretary.Probability.finite_upperTail_real_tendsto hμ b hAtom
  have hRule := B.valueRule_isMeasurable hw.le hc.le
  have hF : Measurable F := Φ.continuous.measurable.comp
    ((((B.valueRule w c).measurable_realizedReward hRule 0).prodMk
      ((B.valueRule w c).measurable_realizedDuration hRule)).prodMk measurable_snd)
  have hBound (q : HybridWorld n Unit) : ‖F q‖≤‖Φ‖ :=
    Φ.norm_coe_le_norm (((B.valueRule w c).realizedReward 0 q,(B.valueRule w c).realizedDuration q),q.2)
  have hInt (Q : Model.Instance n) (η : FiniteMeasure ℝ) : Integrable F (hybridWorldLaw Q η (Measure.dirac ())) :=
    Integrable.of_bound hF.aestronglyMeasurable ‖Φ‖ (Eventually.of_forall hBound)
  have hCountInt (Q : Model.Instance n) (η : FiniteMeasure ℝ) :
      Integrable (fun q => C q*F q) (hybridWorldLaw Q η (Measure.dirac ())) := by
    have hC : Integrable C (hybridWorldLaw Q η (Measure.dirac ())) :=
      (measurePreserving_fst (μ := configurationLaw η) (ν := Q.worldLaw (Measure.dirac ()))).integrable_comp_of_integrable
        (pointCount_integrable η (MeasurableSet.univ.prod measurableSet_Ioi))
    simpa only [mul_comm] using hC.bdd_mul hF.aestronglyMeasurable (Eventually.of_forall hBound)
  have hEq (Q : Model.Instance n) (η : FiniteMeasure ℝ) (a : ℝ) :
      (∫ q, (C q-a)*F q ∂hybridWorldLaw Q η (Measure.dirac ())) =
      (∫ q, C q*F q ∂hybridWorldLaw Q η (Measure.dirac ()))-a*(∫ q, F q ∂hybridWorldLaw Q η (Measure.dirac ())) := by
    have he : (fun q => (C q-a)*F q)=(fun q => C q*F q-a*F q) := by funext q; ring
    rw [he,integral_sub (hCountInt Q η) ((hInt Q η).const_mul a),integral_const_mul]
  have hLimit := hBand.sub (hMass.mul hBase)
  change Tendsto (fun m => ∫ q, (C q-(μs m:Measure ℝ).real (Ioi b))*F q
      ∂hybridWorldLaw (Ps m) (μs m) (Measure.dirac ())) atTop
      (𝓝 (∫ q, (C q-(μ:Measure ℝ).real (Ioi b))*F q ∂hybridWorldLaw P μ (Measure.dirac ())))
  simp_rw [hEq]
  exact hLimit
end ProphetSecretary.Limiting
