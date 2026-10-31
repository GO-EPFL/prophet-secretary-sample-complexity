import ProphetSecretary.Limiting.CoarseFinitePoissonLimit
import ProphetSecretary.Limiting.HybridFixedIndividualScoreWeak

/-!
# First finite-array limit for a retained individual score

The retained score is centered under each actual finite marginal with one
fixed scale. A bounded marked-Poisson comparison and the proved fixed-callback
individual-score weak theorem give the original finite-array test limit.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical BigOperators NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

theorem FiniteIntensityHybridInstance.coarse_finite_individual_observables_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ps : ℕ → Model.Instance n) (sizes : ℕ → ℕ) (Q : ∀ m, Model.Instance (sizes m))
    (d : ℝ) (hd : 0≤d) (H : ℝ≥0)
    (hPCap : ∀ m i, ∀ᵐ x ∂(Ps m).law i, x≤(H:ℝ))
    (hQCap : ∀ m i, ∀ᵐ x ∂(Q m).law i, x≤(H:ℝ))
    (hPWeak : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) atTop (𝓝 (B.individuals.marginalProbabilityLaw i)))
    (hμWeak : Tendsto (fun m => ∑ i, thresholdMarkIntensity ((Q m).law i) d) atTop (𝓝 B.intensity))
    {L : ℝ} (_hL : 0≤L) (δ : ℕ → ℝ) (hδ : ∀ m, 0≤δ m) (hδLim : Tendsto δ atTop (𝓝 (0:ℝ)))
    (hTail : ∀ m, (Q m).tailCount d≤L) (hRare : ∀ m i, ((Q m).law i).real (Ioi d)≤δ m)
    (i : Fin n) (f : ℝ →ᵇ ℝ) (Φ : ((ℝ × ℝ) × Model.World n Unit) →ᵇ ℝ) :
    let π := B.valueThresholdPolicy hw.le hc.le
    Tendsto (fun m => ∫ ω : Model.World (sizes m) (Model.World n Unit),
      centeredBoundedScore ((Ps m).law i) f (ω.2.2.1 i)*hybridOutcomeObservable π Φ
        (thresholdedOfferCountingMeasure d (fun j => (ω.2.1 j,ω.1 j)),ω.2.2)
      ∂(Q m).worldLaw ((Ps m).worldLaw π.seedLaw)) atTop
      (𝓝 (∫ v, centeredBoundedScore (B.individuals.law i) f (v.2.1 i)*
        Φ (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2)
        ∂B.law (Measure.dirac ()))) := by
  let π := B.valueThresholdPolicy hw.le hc.le
  let G := hybridOutcomeObservable π Φ
  let g := fun m (z : (Measure Point) × Model.World n Unit) =>
    centeredBoundedScore ((Ps m).law i) f (z.2.1 i)*G z
  let μ := fun m => ∑ j, thresholdMarkIntensity ((Q m).law j) d
  let A := fun m => ∫ ω : Model.World (sizes m) (Model.World n Unit),
    g m (thresholdedOfferCountingMeasure d (fun j => (ω.2.1 j,ω.1 j)),ω.2.2) ∂(Q m).worldLaw ((Ps m).worldLaw π.seedLaw)
  let C := fun m => ∫ v, g m (countingMeasure v.1,v.2) ∂hybridWorldLaw (Ps m) (μ m) π.seedLaw
  have hG : Measurable G := measurable_hybridOutcomeObservable π Φ Φ.continuous.measurable
  have hGBound (z) : |G z|≤‖Φ‖ := by
    change ‖G z‖≤‖Φ‖
    exact Φ.norm_coe_le_norm
      ((π.rule.observableReward 0 (ProphetSecretary.Probability.finiteMeasureOrZero z.1,z.2),
        π.rule.observableDuration (ProphetSecretary.Probability.finiteMeasureOrZero z.1,z.2)),z.2)
  have hg (m) : Measurable (g m) :=
    (((continuous_centeredBoundedScore ((Ps m).law i) f).measurable.comp
      (by fun_prop : Measurable (fun z : (Measure Point) × Model.World n Unit => z.2.1 i))).mul hG)
  have hgBound (m z) : |g m z|≤‖Φ‖ := by
    change |centeredBoundedScore ((Ps m).law i) f (z.2.1 i)*G z|≤‖Φ‖
    rw [abs_mul]
    exact (mul_le_mul (centeredBoundedScore_abs_le_one ((Ps m).law i) f _) (hGBound z)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hError (m : ℕ) : |A m-C m|≤2*‖Φ‖*(δ m*L) := by
    apply (thresholdedWorld_poisson_observable_error (Q m) ((Ps m).worldLaw π.seedLaw) d (g m) (hg m) (norm_nonneg Φ) (hgBound m)).trans
    exact mul_le_mul_of_nonneg_left (finite_tail_square_sum_le (Q m) d (hδ m) (hTail m) (hRare m)) (by positivity)
  have hRate : Tendsto (fun m => 2*‖Φ‖*(δ m*L)) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,zero_mul] using (hδLim.mul_const L).const_mul (2*‖Φ‖)
  have hDiff : Tendsto (fun m => A m-C m) atTop (𝓝 (0:ℝ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero,Real.norm_eq_abs] using squeeze_zero (fun _ => abs_nonneg _) hError hRate
  have hActual := B.fixed_valueRule_individual_observables_tendsto ha hw hc Ps B.individuals hPWeak hμWeak i f Φ
  have hCEq (m : ℕ) : C m=(∫ v, centeredBoundedScore ((Ps m).law i) f (v.2.1 i)*
      Φ ((π.rule.realizedReward 0 v,π.rule.realizedDuration v),v.2)
      ∂hybridWorldLaw (Ps m) (μ m) π.seedLaw) :=
    integral_congr_ae ((hybridOutcomeObservable_eq_ae π (Ps m) (μ m) H (hPCap m)
      (thresholdMarkIntensity_sum_supported (Q m) hd (hQCap m)) Φ).mono (fun v hv =>
        congrArg (fun x => centeredBoundedScore ((Ps m).law i) f (v.2.1 i)*x) hv))
  have hCLim : Tendsto C atTop (𝓝 (∫ v, centeredBoundedScore (B.individuals.law i) f (v.2.1 i)*
      Φ (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2)
      ∂B.law (Measure.dirac ()))) := by
    have hSeq : C=(fun m => ∫ v, centeredBoundedScore ((Ps m).law i) f (v.2.1 i)*
      Φ ((π.rule.realizedReward 0 v,π.rule.realizedDuration v),v.2)
      ∂hybridWorldLaw (Ps m) (μ m) π.seedLaw) := funext hCEq
    rw [hSeq]
    exact hActual
  change Tendsto A atTop (𝓝 (∫ v, centeredBoundedScore (B.individuals.law i) f (v.2.1 i)*
    Φ (((B.valueRule w c).realizedReward 0 v,(B.valueRule w c).realizedDuration v),v.2) ∂B.law (Measure.dirac ())))
  simpa only [sub_add_cancel,zero_add] using hDiff.add hCLim
end ProphetSecretary.Limiting
