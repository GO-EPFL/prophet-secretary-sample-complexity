import ProphetSecretary.Limiting.HybridFixedCanonicalWeak
import ProphetSecretary.Limiting.PoissonBandCountContinuity

/-!
# Band-count weighted evaluation of a fixed canonical hybrid callback

The complete positive-band count may use points after stopping. At a
continuity boundary its product with every bounded continuous outcome/data
observable has convergent expectation. The zero-intensity case only needs
continuity of the empty branch.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical NNReal
namespace ProphetSecretary.Limiting
variable {n : ℕ}

theorem FiniteIntensityHybridInstance.fixed_valueRule_band_observables_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ps : ℕ → Model.Instance n) (P : Model.Instance n)
    (hP : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) atTop (𝓝 (P.marginalProbabilityLaw i)))
    {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ} (hμ : Tendsto μs atTop (𝓝 μ))
    (b a : ℝ) (hAtom : (μ:Measure ℝ) {b}=0)
    (Φ : ((ℝ × ℝ) × Model.World n Unit) →ᵇ ℝ) :
    Tendsto (fun m => ∫ q, ((pointCount (univ ×ˢ Ioi b) q.1:ℝ)-a)*
        Φ (((B.valueRule w c).realizedReward 0 q,(B.valueRule w c).realizedDuration q),q.2)
      ∂hybridWorldLaw (Ps m) (μs m) (Measure.dirac ())) atTop
      (𝓝 (∫ q, ((pointCount (univ ×ˢ Ioi b) q.1:ℝ)-a)*
        Φ (((B.valueRule w c).realizedReward 0 q,(B.valueRule w c).realizedDuration q),q.2)
        ∂hybridWorldLaw P μ (Measure.dirac ()))) := by
  let F : HybridWorld n Unit → ℝ := fun q => ((pointCount (univ ×ˢ Ioi b) q.1:ℝ)-a)*
    Φ (((B.valueRule w c).realizedReward 0 q,(B.valueRule w c).realizedDuration q),q.2)
  have hRule := B.valueRule_isMeasurable hw.le hc.le
  have hPhiMeas := Φ.continuous.measurable.comp
    ((((B.valueRule w c).measurable_realizedReward hRule 0).prodMk
      ((B.valueRule w c).measurable_realizedDuration hRule)).prodMk measurable_snd)
  have hCountMeas : Measurable (fun q : HybridWorld n Unit => (pointCount (univ ×ˢ Ioi b) q.1:ℝ)) :=
    ((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp
      (measurable_pointCount (MeasurableSet.univ.prod measurableSet_Ioi))).comp measurable_fst
  have hF : Measurable F := (hCountMeas.sub_const a).mul hPhiMeas
  let D := ‖Φ‖*(1+|a|)
  have hD : 0≤D := by dsimp [D]; positivity
  have hBound (q : HybridWorld n Unit) : |F q|≤D*((q.1.1:ℝ)+1) := by
    have hCount : (pointCount (univ ×ˢ Ioi b) q.1:ℝ)≤(q.1.1:ℝ) := by
      exact_mod_cast pointCount_le_count (univ ×ˢ Ioi b) q.1
    have hScore : |(pointCount (univ ×ˢ Ioi b) q.1:ℝ)-a|≤(q.1.1:ℝ)+|a| := by
      have h := abs_sub (pointCount (univ ×ˢ Ioi b) q.1:ℝ) a
      rw [abs_of_nonneg (show 0≤(pointCount (univ ×ˢ Ioi b) q.1:ℝ) from Nat.cast_nonneg _)] at h
      linarith
    have hPhi : |Φ (((B.valueRule w c).realizedReward 0 q,(B.valueRule w c).realizedDuration q),q.2)|≤‖Φ‖ := by
      simpa only [Real.norm_eq_abs] using (Φ.norm_coe_le_norm
        (((B.valueRule w c).realizedReward 0 q,(B.valueRule w c).realizedDuration q),q.2))
    have hPoly : (q.1.1:ℝ)+|a|≤(1+|a|)*((q.1.1:ℝ)+1) := by
      nlinarith [mul_nonneg (abs_nonneg a) (Nat.cast_nonneg (α := ℝ) q.1.1)]
    change |((pointCount (univ ×ˢ Ioi b) q.1:ℝ)-a)*_|≤_
    rw [abs_mul]
    calc
      _ ≤ ((q.1.1:ℝ)+|a|)*‖Φ‖ := mul_le_mul hScore hPhi (abs_nonneg _) (by positivity)
      _ ≤ ((1+|a|)*((q.1.1:ℝ)+1))*‖Φ‖ := mul_le_mul_of_nonneg_right hPoly (norm_nonneg Φ)
      _ = _ := by dsimp [D]; ring
  have hCont (N : ℕ) (hRelevant : μ≠0 ∨ N=0) :
      ∀ᵐ q ∂(arrayLaw μ N).prod (P.worldLaw (Measure.dirac ())),
      ContinuousAt (fun q : (Fin N → Point) × Model.World n Unit => F (configurationMk N q.1,q.2)) q := by
    have hAvoid : ∀ᵐ q ∂(arrayLaw μ N).prod (P.worldLaw (Measure.dirac ())), ∀ j, (q.1 j).2≠b := by
      by_cases hZero : μ=0
      · have hN : N=0 := hRelevant.resolve_left (not_not.mpr hZero)
        subst N
        exact Eventually.of_forall (fun _ j => Fin.elim0 j)
      · have hValue : ∀ᵐ x ∂(μ:Measure ℝ), x≠b := by
          rw [ae_iff]
          have he : {x : ℝ | ¬x≠b}={b} := by ext x; simp
          rw [he]
          exact hAtom
        have hMark : ∀ᵐ p ∂pointLaw μ, p.2≠b :=
          (measurePreserving_snd (μ := Model.Instance.uniformClock) (ν := (μ.normalize:Measure ℝ))).quasiMeasurePreserving.ae
            (normalized_ae μ hZero hValue)
        rw [ae_all_iff]
        intro j
        exact ((measurePreserving_eval (fun _ : Fin N => pointLaw μ) j).comp
          (measurePreserving_fst (μ := arrayLaw μ N) (ν := P.worldLaw (Measure.dirac ())))).quasiMeasurePreserving.ae hMark
    filter_upwards [hAvoid,B.valueRule_branch_payoffs_continuousAt_ae ha hw hc P μ N] with q hAvoid hq
    have hCount := (pointCount_upperBand_branch_continuousAt b q.1 hAvoid).comp'
      (f := (Prod.fst : ((Fin N → Point) × Model.World n Unit) → (Fin N → Point))) continuous_fst.continuousAt
    have hPhi := Φ.continuous.continuousAt.comp'
      (f := fun z : (Fin N → Point) × Model.World n Unit =>
        (((B.valueRule w c).realizedReward 0 (configurationMk N z.1,z.2),
          (B.valueRule w c).realizedDuration (configurationMk N z.1,z.2)),z.2))
      ((hq.1.prodMk hq.2).prodMk continuous_snd.continuousAt)
    exact (hCount.sub_const a).mul hPhi
  exact poissonObservable_integral_tendsto_of_relevant_branches hμ
    (retainedWorldProbabilityLaw_tendsto Ps P hP) F hF hD hBound hCont
end ProphetSecretary.Limiting
