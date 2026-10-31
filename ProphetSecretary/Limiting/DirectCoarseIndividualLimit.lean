import ProphetSecretary.Limiting.CoarseFiniteIndividualOutcomes
import ProphetSecretary.Limiting.DirectCoarseExpectedScores
import ProphetSecretary.Limiting.DirectCoarseScoreIdentities
import ProphetSecretary.Limiting.TruncatedScoreLimits
import ProphetSecretary.Limiting.DirectIndividualScore
import ProphetSecretary.Limiting.IidSquareRarity

/-!
# Actual retained-individual direct coarse covariances

Both the retained prefix and the fixed virtual count may grow. At a fixed
coarse prefix and cutoff, the actual retained-individual score is transported
through causal identity projection, then its finite-array limit is taken.
Only positive-band control is used, without a bound on the total first moment.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

theorem CountableInstance.direct_coarse_individual_score_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (ret N : ℕ → ℕ) (hRet : Tendsto ret atTop atTop) (hN : ∀ m, 0<N m)
    (κ : ℕ → Measure ℝ) [∀ m, IsProbabilityMeasure (κ m)]
    (hκ : ∀ m, ∀ᵐ x ∂κ m, 0≤x) (hCap : ∀ m, ∀ᵐ x ∂κ m, x≤(B.cap:ℝ))
    (K : ℕ) (d : ℝ) (hd : 0<d)
    (hμWeak : Tendsto (fun m => ∑ _i : Fin (N m), thresholdMarkIntensity (κ m) d) atTop
      (𝓝 (B.intensityAbove d (by simpa only [hZero,NNReal.coe_zero] using hd))))
    {L : ℝ} (hL : 0≤L) (hTail : ∀ m, (N m:ℝ)*(κ m).real (Ioi d)≤L)
    (hSquares : Tendsto (fun m => (N m:ℝ)*((κ m).real (Ioi d))^2) atTop (𝓝 (0:ℝ)))
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (i : Fin K) (f : ℝ →ᵇ ℝ) :
    let D := B.truncation K d (by simpa only [hZero,NNReal.coe_zero] using hd)
    let π := D.valueThresholdPolicy hw.le hc.le
    let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
    let P := fun m => (B.individualPrefix (ret m)).appendIndependent (Q m)
    Tendsto (fun m => (directCoarsePolicy (ret m) (N m) π d).expectedRewardScore (P m)
      (directIndividualScore (B.individualPrefix (ret m)) (Q m) i.val f)) atTop
      (𝓝 (∫ v, centeredBoundedScore (B.individuals i.val:Measure ℝ) f (v.2.1 i)*
        (D.valueRule w c).realizedReward 0 v ∂D.law (Measure.dirac ()))) ∧
    Tendsto (fun m => (directCoarsePolicy (ret m) (N m) π d).expectedDurationScore (P m)
      (directIndividualScore (B.individualPrefix (ret m)) (Q m) i.val f)) atTop
      (𝓝 (∫ v, centeredBoundedScore (B.individuals i.val:Measure ℝ) f (v.2.1 i)*
        (D.valueRule w c).realizedDuration v ∂D.law (Measure.dirac ()))) := by
  have hdAbove : (B.terminal:ℝ)<d := by simpa only [hZero,NNReal.coe_zero] using hd
  let D := B.truncation K d hdAbove
  let π := D.valueThresholdPolicy hw.le hc.le
  let Ps := B.individualPrefix K
  let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
  let s := fun m (y : Fin (K+N m) → ℝ) => centeredBoundedScore (Ps.law i) f (y (i.castAdd (N m)))
  have hPs (j) : ∀ᵐ x ∂Ps.law j, x≤(B.cap:ℝ) := (B.individual_supported j.val).mono (fun _ hx => hx.2)
  let δ := fun m => (κ m).real (Ioi d)
  have hTailQ (m) : (Q m).tailCount d≤L := by
    simpa only [Q,Model.Instance.tailCount,Model.iidOfferInstance,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,Measure.real] using hTail m
  have hLim := D.coarse_finite_individual_outcomes_tendsto hZero hw hc (fun _ => Ps) N Q d hd.le B.cap (le_refl _)
    (fun _ => hPs) (fun m _ => hCap m) (fun _ => tendsto_const_nhds) hμWeak hL δ
    (fun _ => measureReal_nonneg) (iid_band_probability_tendsto_zero N hN κ (Ioi d) hSquares)
    hTailQ (fun _ _ => le_refl _) i f
  have hs (m) : Measurable (s m) :=
    (continuous_centeredBoundedScore (Ps.law i) f).measurable.comp (measurable_pi_apply (i.castAdd (N m)))
  let g := fun v : Model.World K π.Seed => centeredBoundedScore (Ps.law i) f (v.1 i)
  have hg : Measurable g := (continuous_centeredBoundedScore (Ps.law i) f).measurable.comp
    ((measurable_pi_apply i).comp measurable_fst)
  have hgb (v) : ‖g v‖≤1 := centeredBoundedScore_abs_le_one (Ps.law i) f (v.1 i)
  have hExec (m) := π.finiteCutoffEvaluation_retained_score_coordinate_tests Ps (Q m) d B.cap hPs (fun _ => hCap m) g hg hgb
  have hSplit (m) (hm : K≤ret m) : (B.individualPrefix (ret m)).restrictBy (Fin.castLEEmb hm)=Ps := by
    apply Model.Instance.eq_of_law_eq
    rfl
  have hOrig (m) (hm : K≤ret m) : directIndividualScore (B.individualPrefix (ret m)) (Q m) i.val f=
      individualContinuousScore ((B.individualPrefix (ret m)).appendIndependent (Q m)).law
        ((Fin.castLE hm i).castAdd (N m)) f := by
    have hi : i.val<ret m := i.isLt.trans_le hm
    unfold directIndividualScore
    rw [dif_pos hi]
    have hIdx : ((⟨i.val,hi⟩:Fin (ret m)).castAdd (N m))=(Fin.castLE hm i).castAdd (N m) := by
      apply Fin.ext
      rfl
    exact congrArg (fun j => individualContinuousScore ((B.individualPrefix (ret m)).appendIndependent (Q m)).law j f) hIdx
  have hEq (m) (hm : K≤ret m) := directCoarsePolicy_expectedScores_of_pullback
    (B.individualPrefix (ret m)) (Q m) hm π d (s m) (hs m)
    (directIndividualScore (B.individualPrefix (ret m)) (Q m) i.val f)
    (fun x => by
      rw [hOrig m hm]
      have hPull := directCoarseScore_individual_pullback (B.individualPrefix (ret m)) (Q m) hm i f x
      rw [hSplit m hm] at hPull
      exact hPull)
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
