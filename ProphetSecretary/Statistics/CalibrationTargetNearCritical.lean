import ProphetSecretary.Statistics.CalibrationTargetAccuracy
import ProphetSecretary.Statistics.CalibrationAdaptation
import ProphetSecretary.Statistics.EmpiricalGapKernel

/-!
# Near-critical accuracy of the finite calibration target

At a fixed true-law ratio minimizer, the sampled numerator is the sum of a
centered frozen-policy kernel, empirical adaptation gain, and a benchmark
estimation term multiplied by the ratio slack. This is the small-gap part
of `lem:calibration-target`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Statistics.Hoeffding

variable {n m : ℕ} [NeZero m]

/-- The near-critical sampled numerator bounds the actual finite target on accurate queries. -/
lemma numericalTarget_sharp_pointwise (π : RandomizedPolicy n) (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1)
    (mu : ℝ) (hmu : 0 < mu) (hMean : mu ≤ P.expectedMaximum)
    (y : (Fin n × Fin m) → ℝ) (v : TargetGrid m → ℝ)
    (hy : ∀ q, y q ∈ Icc (0 : ℝ) 1)
    (hEligible : targetEligible mu y) (hGood : ¬queryFailure mu y v)
    {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1)
    (hz : (1-lam)/lam ∈ Icc (0 : ℝ) 4)
    (hmin : P.optimalScalarRatio=P.normalizedScalarRatio lam) :
    max 0 (numericalTarget mu y v-P.optimalScalarRatio) ≤
      (2/mu)*(|empiricalMean (π.normalizedGameKernel lam) y-normalizedScalarGap P lam|+
        frozenAdaptation π lam y+(P.optimalScalarRatio-optimalCompetitiveRatio)*
          |trainingExpectedMaximum y-P.expectedMaximum|)+6/(mu*(m : ℝ)) := by
  let Q := trainingInstance y
  let z := (1-lam)/lam
  let g := P.optimalScalarRatio-optimalCompetitiveRatio
  let U := |empiricalMean (π.normalizedGameKernel lam) y-normalizedScalarGap P lam|+
    frozenAdaptation π lam y+g*|trainingExpectedMaximum y-P.expectedMaximum|
  have h01 : lam ∈ Icc (0 : ℝ) 1 := ⟨hlam.1.le, hlam.2⟩
  have hGamma := P.optimalScalarRatio_bounds hP
  have hHalf : (1/2 : ℝ) ≤ P.optimalScalarRatio := half_le_optimalCompetitiveRatio.trans hGamma.1
  have hg0 : 0 ≤ g := sub_nonneg.mpr hGamma.1
  have hM : 0 < trainingExpectedMaximum y := by linarith [hEligible.2]
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hQ : Q.HasPositiveFiniteMaximum := ⟨totalEmpiricalInstance_integrable _, hM⟩
  have hU0 : 0 ≤ U := add_nonneg
    (add_nonneg (abs_nonneg _) (frozenAdaptation_nonnegative π h01 y)) (mul_nonneg hg0 (abs_nonneg _))
  have hAcc : ∀ j, v j ≤ optimalScalarValue Q 1 (targetGrid j)+1/(m : ℝ) := by
    intro j
    have hAll : ∀ j, |v j-optimalScalarValue Q 1 (targetGrid j)| ≤ 1/(m : ℝ) := by
      by_contra hn
      exact hGood ⟨hEligible, hn⟩
    linarith [(abs_le.mp (hAll j)).2]
  have hMin := targetMinimumRatio_le_at y v hM hz hAcc
  have hClip := numericalTarget_positive_error_le_minimum mu y v hEligible hHalf
  have hK : empiricalMean (π.normalizedGameKernel lam) y =
      π.scalarObjective Q lam (1-lam)-optimalCompetitiveRatio*(lam*trainingExpectedMaximum y+1-lam) := by
    rw [π.empiricalMean_normalizedGameKernel hlam y hy]
    change π.scalarObjective Q lam (1-lam)-optimalCompetitiveRatio*(lam*trainingExpectedMaximum y+(1-lam)) = _
    ring
  have hDec := π.calibrationRatio_numerator_decomposition P Q hP h01 hmin
  change optimalScalarValue Q lam (1-lam)-P.optimalScalarRatio*(lam*trainingExpectedMaximum y+1-lam) =
      (π.scalarObjective Q lam (1-lam)-optimalCompetitiveRatio*(lam*trainingExpectedMaximum y+1-lam))-
      normalizedScalarGap P lam+frozenAdaptation π lam y-g*lam*(trainingExpectedMaximum y-P.expectedMaximum) at hDec
  rw [← hK] at hDec
  have hN : optimalScalarValue Q lam (1-lam)-P.optimalScalarRatio*(lam*trainingExpectedMaximum y+1-lam) ≤ U := by
    have hF := le_abs_self (empiricalMean (π.normalizedGameKernel lam) y-normalizedScalarGap P lam)
    have hOne := mul_le_mul_of_nonneg_left (neg_le_abs (trainingExpectedMaximum y-P.expectedMaximum))
      (mul_nonneg hg0 hlam.1.le)
    have hTwo := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlam.2 hg0)
      (abs_nonneg (trainingExpectedMaximum y-P.expectedMaximum))
    rw [hDec]
    dsimp [U]
    nlinarith
  have hDen : mu/2 ≤ lam*trainingExpectedMaximum y+1-lam := by
    apply Q.scalarRatio_denominator_ge _ hEligible.2 h01
    have hM1 := P.expectedMaximum_le_of_bounded zero_le_one hcap
    linarith
  have hDpos : 0 < lam*trainingExpectedMaximum y+1-lam := (div_pos hmu (by norm_num : (0 : ℝ)<2)).trans_le hDen
  have heLam : 1/(1+z)=lam := by dsimp [z]; field_simp [hlam.1.ne']; ring
  have hNorm := Q.normalizedScalarRatio_eq_durationScalarRatio hQ hz.1
  rw [heLam] at hNorm
  have hRatio : Q.durationScalarRatio z-P.optimalScalarRatio ≤ (2/mu)*U := by
    rw [← hNorm]
    have he : Q.normalizedScalarRatio lam-P.optimalScalarRatio =
        (optimalScalarValue Q lam (1-lam)-P.optimalScalarRatio*(lam*trainingExpectedMaximum y+1-lam))/
          (lam*trainingExpectedMaximum y+1-lam) := by
      change optimalScalarValue Q lam (1-lam)/(lam*trainingExpectedMaximum y+1-lam)-P.optimalScalarRatio = _
      field_simp [hDpos.ne']
    rw [he]
    have h := (div_le_div_of_nonneg_right hN hDpos.le).trans
      (div_le_div_of_nonneg_left hU0 (div_pos hmu (by norm_num : (0 : ℝ)<2)) hDen)
    apply h.trans_eq
    field_simp
  have hPrec : 3/((m : ℝ)*trainingExpectedMaximum y) ≤ 6/(mu*(m : ℝ)) := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤3)
      (mul_pos hm (div_pos hmu (by norm_num : (0 : ℝ)<2)))
      (mul_le_mul_of_nonneg_left hEligible.2 hm.le)
    apply h.trans_eq
    field_simp
    ring
  have hRaw : targetMinimumRatio y v-P.optimalScalarRatio ≤ (2/mu)*U+6/(mu*(m : ℝ)) := by
    linarith [hMin, hRatio, hPrec]
  have hNonneg : 0 ≤ (2/mu)*U+6/(mu*(m : ℝ)) := by positivity
  exact hClip.trans (max_le hNonneg hRaw)

/-- Expected small-gap error, with the three exceptional probabilities still explicit. -/
theorem numericalTarget_expected_sharp_components {Seed : Type*} [MeasurableSpace Seed]
    (π : RandomizedPolicy n) (P : Instance n) (hP : P.HasPositiveFiniteMaximum)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (mu : ℝ) (hmu : 0 < mu) (hMean : mu ≤ P.expectedMaximum)
    (out : (((Fin n × Fin m) → ℝ) × Seed) → TargetGrid m → ℝ) (ho : Measurable out)
    {δ lam lo hi : ℝ} (hδ : 0 < δ) (hlam : lam ∈ Icc δ (1-δ)) (hLamLow : (4/5 : ℝ) ≤ lam)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hzRange : (1-lam)/lam ∈ Icc lo hi)
    (hmin : P.optimalScalarRatio=P.normalizedScalarRatio lam)
    (hOpt : π.scalarObjective P lam (1-lam)=optimalScalarValue P lam (1-lam)) :
    (∫ p, max 0 (numericalTarget mu p.1 (out p)-P.optimalScalarRatio)
      ∂(P.trainingCoordinateLaw m).prod ν) ≤
      (2/mu)*(Real.sqrt (pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)*
        (P.optimalScalarRatio-optimalCompetitiveRatio)/(m : ℝ)+1/(m : ℝ)^2)+
      empiricalCandidateRegretConstant lo hi*P.totalFirstMoment*(1+P.totalFirstMoment)/(m : ℝ)+
      (P.optimalScalarRatio-optimalCompetitiveRatio)*Real.sqrt (P.expectedMaximum/(m : ℝ)))+
      6/(mu*(m : ℝ))+
      (P.trainingCoordinateLaw m).real {a | targetCountCutoff m < empiricalPositiveCount a}+
      (P.trainingCoordinateLaw m).real {a | trainingExpectedMaximum a < mu/2}+
      ((P.trainingCoordinateLaw m).prod ν).real {p | queryFailure mu p.1 (out p)} := by
  let g := P.optimalScalarRatio-optimalCompetitiveRatio
  let fK : ((Fin n × Fin m) → ℝ) → ℝ := fun a =>
    |empiricalMean (π.normalizedGameKernel lam) a-normalizedScalarGap P lam|
  let fD := frozenAdaptation (m := m) π lam
  let fM : ((Fin n × Fin m) → ℝ) → ℝ := fun a => |trainingExpectedMaximum a-P.expectedMaximum|
  let A : ((Fin n × Fin m) → ℝ) → ℝ := fun a => (2/mu)*(fK a+fD a+g*fM a)+6/(mu*(m : ℝ))
  have hLam : lam ∈ Ioc (0 : ℝ) 1 := ⟨hδ.trans_le hlam.1, by linarith [hlam.2]⟩
  have h01 : lam ∈ Icc (0 : ℝ) 1 := ⟨hLam.1.le, hLam.2⟩
  have hg0 : 0 ≤ g := sub_nonneg.mpr (P.optimalScalarRatio_bounds hP).1
  have hz : (1-lam)/lam ∈ Icc (0 : ℝ) 4 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hLam.2) hLam.1.le, ?_⟩
    apply (div_le_iff₀ hLam.1).mpr
    linarith
  have hf := π.measurable_normalizedGameKernel lam
  have hb := π.normalizedGameKernel_abs_le_ae P hcap hLam
  have hKLP := memLp_empiricalMean_of_ae_bounded (k := m) P.law hf 1 hb 2
  have hKI : Integrable fK (P.trainingCoordinateLaw m) :=
    (hKLP.sub (memLp_const (normalizedScalarGap P lam))).abs.integrable (by norm_num)
  have hDI : Integrable fD (P.trainingCoordinateLaw m) := integrable_frozenAdaptation π P hcap hLam
  have hMI : Integrable fM (P.trainingCoordinateLaw m) :=
    (((P.memLp_empiricalExpectedMaximum (k := m) 1 hcap 2).integrable (by norm_num)).sub (integrable_const _)).abs
  have hAI : Integrable A (P.trainingCoordinateLaw m) :=
    (((hKI.add hDI).add (hMI.const_mul g)).const_mul (2/mu)).add (integrable_const _)
  have hA0 (a) : 0 ≤ A a := by
    dsimp only [A, fK, fD, fM]
    have hD := frozenAdaptation_nonnegative π h01 a
    positivity
  have hUnit : ∀ᵐ a ∂P.trainingCoordinateLaw m, ∀ q, a q ∈ Icc (0 : ℝ) 1 := by
    apply ae_all_iff.mpr
    intro q
    have hp := measurePreserving_eval (fun q : Fin n × Fin m => P.law q.1) q
    filter_upwards [hp.quasiMeasurePreserving.ae (P.nonnegative q.1),
      hp.quasiMeasurePreserving.ae (hcap q.1)] with a ha0 ha1
    exact ⟨ha0, ha1⟩
  have hUnitProd := (measurePreserving_fst : MeasurePreserving
    (Prod.fst : (((Fin n × Fin m) → ℝ) × Seed) → _) ((P.trainingCoordinateLaw m).prod ν)
      (P.trainingCoordinateLaw m)).quasiMeasurePreserving.ae hUnit
  have h := target_error_integral_le_of_pointwise P hP ν mu out ho A hAI hA0 (by
    filter_upwards [hUnitProd] with p hp
    exact fun hEligible hGood => numericalTarget_sharp_pointwise π P hP hcap mu hmu hMean
      p.1 (out p) hp hEligible hGood hLam hz hmin)
  have heA : (∫ a, A a ∂P.trainingCoordinateLaw m) =
      (2/mu)*((∫ a, fK a ∂P.trainingCoordinateLaw m)+(∫ a, fD a ∂P.trainingCoordinateLaw m)+
        g*(∫ a, fM a ∂P.trainingCoordinateLaw m))+6/(mu*(m : ℝ)) := by
    change (∫ a, (2/mu)*(fK a+fD a+g*fM a)+6/(mu*(m : ℝ)) ∂P.trainingCoordinateLaw m) = _
    rw [integral_add (f := fun a => (2/mu)*(fK a+fD a+g*fM a))
        (g := fun _ => 6/(mu*(m : ℝ))) (((hKI.add hDI).add (hMI.const_mul g)).const_mul (2/mu)) (integrable_const _),
      integral_const_mul, integral_add (f := fun a => fK a+fD a) (g := fun a => g*fM a)
        (hKI.add hDI) (hMI.const_mul g), integral_add (f := fK) (g := fD) hKI hDI,
      integral_const_mul, integral_const, probReal_univ, one_smul]
  have hM1 := P.expectedMaximum_le_of_bounded zero_le_one hcap
  have hKernel := π.empiricalGameKernel_L1_error_le_ratioSlack (k := m) P hP hcap hM1 hδ hlam hmin hOpt
  have hAdapt := integral_frozenAdaptation_le (m := m) π P hcap hLam hlo hlohi hzRange hOpt
  have hMax := P.empiricalMaximum_L1_error_le (k := m) hcap
  have hStat := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hKernel hAdapt)
    (mul_le_mul_of_nonneg_left hMax hg0)) (by positivity : (0 : ℝ) ≤ 2/mu)
  change (2/mu)*((∫ a, fK a ∂P.trainingCoordinateLaw m)+(∫ a, fD a ∂P.trainingCoordinateLaw m)+
    g*(∫ a, fM a ∂P.trainingCoordinateLaw m)) ≤ _ at hStat
  rw [heA] at h
  linarith

private lemma sqrt_variance_linear_bound {C g k : ℝ} (hC : 0 ≤ C) (hg : 0 ≤ g) (hk : 0 < k) :
    Real.sqrt (C*g/k+1/k^2) ≤ Real.sqrt C*Real.sqrt (g/k)+1/k := by
  have hs : 0 ≤ g/k := div_nonneg hg hk.le
  have hu : 0 ≤ Real.sqrt C*Real.sqrt (g/k) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hv : 0 ≤ 1/k := by positivity
  have hU : (Real.sqrt C*Real.sqrt (g/k))^2=C*g/k := by
    rw [mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hs]
    ring
  have hV : (1/k)^2=1/k^2 := by ring
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg hu hv, ?_⟩
  nlinarith [mul_nonneg hu hv]

private lemma ratioSlack_maximum_error_bound {g M k : ℝ}
    (hg : 0 ≤ g) (hg1 : g ≤ 1) (hM : M ≤ 1) (hk : 0 < k) :
    g*Real.sqrt (M/k) ≤ Real.sqrt (g/k) := by
  have hRoot : Real.sqrt (M/k) ≤ 1/Real.sqrt k := by
    calc
      _ ≤ Real.sqrt (1/k) := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hM hk.le)
      _ = _ := by rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
  have hG : g ≤ Real.sqrt g := Real.le_sqrt_self_iff.mpr hg1
  calc
    _ ≤ g*(1/Real.sqrt k) := mul_le_mul_of_nonneg_left hRoot hg
    _ ≤ Real.sqrt g*(1/Real.sqrt k) := mul_le_mul_of_nonneg_right hG (by positivity)
    _ = _ := by rw [Real.sqrt_div hg]; ring

private lemma sample_sharp_remainder_bounds :
    1/(m : ℝ)^2 ≤ 1/(m : ℝ) ∧ Real.exp (-2*(m : ℝ)) ≤ 1/(m : ℝ) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  refine ⟨one_div_le_one_div_of_le hm (by nlinarith), ?_⟩
  have hExp : (m : ℝ) ≤ Real.exp (2*(m : ℝ)) := by linarith [Real.add_one_le_exp (2*(m : ℝ))]
  calc
    Real.exp (-2*(m : ℝ)) = 1/Real.exp (2*(m : ℝ)) := by simp only [neg_mul, Real.exp_neg, one_div]
    _ ≤ _ := one_div_le_one_div_of_le hm hExp

/-- Explicit sharp constants when the deterministic minimizing weight is in a fixed interior interval. -/
theorem numericalTarget_expected_sharp_on_interior {Seed : Type*} [MeasurableSpace Seed]
    (π : RandomizedPolicy n) (P : Instance n) (hP : P.HasPositiveFiniteMaximum)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (mu : ℝ) (hmu : 0 < mu) (hMean : mu ≤ P.expectedMaximum)
    (hCount : P.positiveCount ≤ 2*Real.log (m : ℝ))
    (out : (((Fin n × Fin m) → ℝ) × Seed) → TargetGrid m → ℝ) (ho : Measurable out)
    (hConf : ∀ᵐ a ∂P.trainingCoordinateLaw m, targetEligible mu a → ∀ j : TargetGrid m,
      ν.real {r | 1/(m : ℝ) < |out (a,r) j-optimalScalarValue (trainingInstance a) 1 (targetGrid j)|} ≤
        1/((m : ℝ)^2*(4*(m : ℝ)+1)))
    {δ lam lo hi S0 : ℝ} (hδ : 0 < δ) (hlam : lam ∈ Icc δ (1-δ)) (hLamLow : (4/5 : ℝ) ≤ lam)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hzRange : (1-lam)/lam ∈ Icc lo hi)
    (hS0 : 0 ≤ S0) (hS : P.totalFirstMoment ≤ S0)
    (hmin : P.optimalScalarRatio=P.normalizedScalarRatio lam)
    (hOpt : π.scalarObjective P lam (1-lam)=optimalScalarValue P lam (1-lam)) :
    (∫ p, max 0 (numericalTarget mu p.1 (out p)-P.optimalScalarRatio)
      ∂(P.trainingCoordinateLaw m).prod ν) ≤
      ((2/mu)*(Real.sqrt (pilotFirstProjectionConstant δ*(1+S0))+1))*
        Real.sqrt ((P.optimalScalarRatio-optimalCompetitiveRatio)/(m : ℝ))+
      ((2/mu)*(1+empiricalCandidateRegretConstant lo hi*S0*(1+S0))+10/mu+2)/(m : ℝ) := by
  let g := P.optimalScalarRatio-optimalCompetitiveRatio
  let Cv := pilotFirstProjectionConstant δ*(1+S0)
  let Cr := empiricalCandidateRegretConstant lo hi*S0*(1+S0)
  have hg : 0 ≤ g := sub_nonneg.mpr (P.optimalScalarRatio_bounds hP).1
  have hg1 : g ≤ 1 := by
    have hGamma := (P.optimalScalarRatio_bounds hP).2
    dsimp [g]
    linarith [optimalCompetitiveRatio_nonnegative]
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hCv0 : 0 ≤ Cv := by
    have hC := (pilotFirstProjectionConstant_positive hδ).le
    dsimp [Cv]
    positivity
  have hCr0 : 0 ≤ Cr := by
    have hC := (empiricalCandidateRegretConstant_positive hlo hlohi).le
    dsimp [Cr]
    positivity
  have hComp := numericalTarget_expected_sharp_components π P hP hcap ν mu hmu hMean out ho
    hδ hlam hLamLow hlo hlohi hzRange hmin hOpt
  have hCvar := (pilotFirstProjectionConstant_positive hδ).le
  have hVarScale := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hS) hCvar) hg) hm.le
  have hRoot : Real.sqrt (pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)*g/(m : ℝ)+1/(m : ℝ)^2) ≤
      Real.sqrt Cv*Real.sqrt (g/(m : ℝ))+1/(m : ℝ) :=
    (Real.sqrt_le_sqrt (add_le_add hVarScale (le_refl (1/(m : ℝ)^2)))).trans (sqrt_variance_linear_bound hCv0 hg hm)
  have hCS := (empiricalCandidateRegretConstant_positive hlo hlohi).le
  have hSNonneg := P.totalFirstMoment_nonnegative
  have hSS : P.totalFirstMoment*(1+P.totalFirstMoment) ≤ S0*(1+S0) :=
    mul_le_mul hS (add_le_add le_rfl hS) (by positivity) hS0
  have hRegret : empiricalCandidateRegretConstant lo hi*P.totalFirstMoment*(1+P.totalFirstMoment)/(m : ℝ) ≤ Cr/(m : ℝ) := by
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSS hCS) hm.le
    calc
      _ = (empiricalCandidateRegretConstant lo hi*(P.totalFirstMoment*(1+P.totalFirstMoment)))/(m : ℝ) := by ring
      _ ≤ (empiricalCandidateRegretConstant lo hi*(S0*(1+S0)))/(m : ℝ) := h
      _ = Cr/(m : ℝ) := by dsimp [Cr]; ring
  have hMax := ratioSlack_maximum_error_bound hg hg1 (P.expectedMaximum_le_of_bounded zero_le_one hcap) hm
  have hBase := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hRoot hRegret) hMax)
    (by positivity : (0 : ℝ) ≤ 2/mu)
  have hCountBound := empiricalPositiveCount_cutoff_probability (m := m) P hCount
  have hMeanBound := P.empiricalMaximum_small_probability (k := m) hcap hmu hMean
  change (P.trainingCoordinateLaw m).real {a | trainingExpectedMaximum a < mu/2} ≤
    4/(mu*(m : ℝ)) at hMeanBound
  have hQueryBound := queryFailure_probability_le (P.trainingCoordinateLaw m) ν mu out ho hConf
  obtain ⟨hInv, hExp⟩ := sample_sharp_remainder_bounds (m := m)
  have hAll := add_le_add (add_le_add (add_le_add (add_le_add hBase (le_refl (6/(mu*(m : ℝ)))))
    (hCountBound.trans hExp)) hMeanBound) (hQueryBound.trans hInv)
  exact hComp.trans (hAll.trans_eq (by dsimp [Cv, Cr, g]; ring))

end ProphetSecretary.Statistics.Calibration
