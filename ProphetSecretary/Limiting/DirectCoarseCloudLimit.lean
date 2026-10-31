import ProphetSecretary.Limiting.CoarseFiniteZeroAtomOutcomes
import ProphetSecretary.Limiting.DirectCoarseExpectedScores
import ProphetSecretary.Limiting.DirectCoarseScoreIdentities
import ProphetSecretary.Limiting.TruncatedScoreLimits

/-!
# Actual direct-approximation coarse cloud covariances

Both the retained prefix and the fixed virtual count may grow. At a fixed
coarse prefix and cutoff, the actual complete zero-atom score is transported
through causal identity projection, then its finite-array limit is taken.
Only positive-band control is used, without a bound on the total first moment.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

theorem CountableInstance.direct_coarse_cloud_score_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (ret N : ℕ → ℕ) (hRet : Tendsto ret atTop atTop) (hN : ∀ m, 0<N m)
    (hNLim : Tendsto (fun m => (N m:ℝ)) atTop atTop)
    (κ : ℕ → Measure ℝ) [∀ m, IsProbabilityMeasure (κ m)]
    (hκ : ∀ m, ∀ᵐ x ∂κ m, 0≤x) (hCap : ∀ m, ∀ᵐ x ∂κ m, x≤(B.cap:ℝ))
    (K : ℕ) (d b : ℝ) (hd : 0<d) (hdb : d≤b) (hAtom : B.intensity {b}=0)
    (hμWeak : Tendsto (fun m => ∑ _i : Fin (N m), thresholdMarkIntensity (κ m) d) atTop
      (𝓝 (B.intensityAbove d (by simpa only [hZero,NNReal.coe_zero] using hd))))
    (hq : ∀ m, (1/2:ℝ)≤(κ m).real {0})
    (hp : ∀ m, (κ m).real (Ioi b)=B.intensity.real (Ioi b)/(N m:ℝ))
    (hSquares : Tendsto (fun m => (N m:ℝ)*((κ m).real (Ioi d))^2) atTop (𝓝 (0:ℝ)))
    {w c : ℝ} (hw : 0<w) (hc : 0<c) :
    let D := B.truncation K d (by simpa only [hZero,NNReal.coe_zero] using hd)
    let π := D.valueThresholdPolicy hw.le hc.le
    let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
    let P := fun m => (B.individualPrefix (ret m)).appendIndependent (Q m)
    Tendsto (fun m => (directCoarsePolicy (ret m) (N m) π d).expectedRewardScore (P m)
      (directCloudScore (ret m) (N m) (κ m) (Ioi b))) atTop
      (𝓝 (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-B.intensity.real (Ioi b))*
        (D.valueRule w c).realizedReward 0 v ∂D.law (Measure.dirac ()))) ∧
    Tendsto (fun m => (directCoarsePolicy (ret m) (N m) π d).expectedDurationScore (P m)
      (directCloudScore (ret m) (N m) (κ m) (Ioi b))) atTop
      (𝓝 (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-B.intensity.real (Ioi b))*
        (D.valueRule w c).realizedDuration v ∂D.law (Measure.dirac ()))) := by
  have hdAbove : (B.terminal:ℝ)<d := by simpa only [hZero,NNReal.coe_zero] using hd
  let D := B.truncation K d hdAbove
  let π := D.valueThresholdPolicy hw.le hc.le
  let Ps := B.individualPrefix K
  let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
  let s := fun m => completeScore (fun _ : Fin (N m) => ProphetSecretary.Probability.bandScore (κ m) (Ioi b))
  have hPs (i) : ∀ᵐ x ∂Ps.law i, x≤(B.cap:ℝ) := (B.individual_supported i.val).mono (fun _ hx => hx.2)
  have hAtomD : (D.intensity:Measure ℝ) {b}=0 := by
    change B.intensity.restrict (Ioi d) {b}=0
    rw [Measure.restrict_apply (measurableSet_singleton b)]
    exact measure_mono_null inter_subset_left hAtom
  have hCenter : (D.intensity:Measure ℝ).real (Ioi b)=B.intensity.real (Ioi b) := B.intensityAbove_real_upper hdAbove b hdb
  have hpD (m) : (κ m).real (Ioi b)=(D.intensity:Measure ℝ).real (Ioi b)/(N m:ℝ) := by rw [hCenter];exact hp m
  have hLim := D.coarse_finite_zeroAtom_outcomes_tendsto hZero hw hc (fun _ => Ps) N hN hNLim κ hκ d b hd.le hdb B.cap
    (le_refl _) (fun _ => hPs) hCap (fun _ => tendsto_const_nhds) hμWeak hAtomD (hd.trans_le hdb) hq hpD hSquares
  rw [hCenter] at hLim
  have hs (m) : Measurable (s m) := measurable_completeScore (fun _ => ProphetSecretary.Probability.measurable_bandScore (κ m) measurableSet_Ioi)
  have hsInt (m) : Integrable (s m) (Q m).valuesLaw := by
    simpa only [s,Q,Model.iidOfferInstance,Model.Instance.valuesLaw,pow_one] using
      completeBandScore_integrable_pow (κ m) measurableSet_Ioi (not_lt.mpr (hd.le.trans hdb)) (hq m) (N m) 1
  have hExec (m) := π.finiteCutoffEvaluation_score_coordinate_tests Ps (Q m) d B.cap hPs (fun _ => hCap m)
    (s m) (hs m) (hsInt m)
  have hSplit (m) (hm : K≤ret m) : (B.individualPrefix (ret m)).restrictBy (Fin.castLEEmb hm)=Ps := by
    apply Model.Instance.eq_of_law_eq
    rfl
  have hEq (m) (hm : K≤ret m) := directCoarsePolicy_expectedScores_of_pullback
    (B.individualPrefix (ret m)) (Q m) hm π d
    (fun y : Fin (K+N m) → ℝ => s m (fun j => y (j.natAdd K)))
    ((hs m).comp (measurable_pi_lambda _ (fun j => measurable_pi_apply (j.natAdd K))))
    (directCloudScore (ret m) (N m) (κ m) (Ioi b))
    (directCoarseScore_cloud_pullback (N := N m) hm (κ m) (Ioi b))
    (by rw [hSplit m hm];exact (hExec m).1.1)
    (by rw [hSplit m hm];exact (hExec m).2.1)
  constructor
  · apply hLim.1.congr'
    filter_upwards [hRet (eventually_ge_atTop K)] with m hm
    have hE := (hEq m hm).1
    rw [hSplit m hm] at hE
    exact hE.symm
  · apply hLim.2.congr'
    filter_upwards [hRet (eventually_ge_atTop K)] with m hm
    have hE := (hEq m hm).2
    rw [hSplit m hm] at hE
    exact hE.symm
end ProphetSecretary.Limiting
