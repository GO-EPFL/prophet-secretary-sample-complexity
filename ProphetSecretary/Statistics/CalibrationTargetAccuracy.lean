import ProphetSecretary.Statistics.CalibrationNumericalTarget
import ProphetSecretary.Statistics.CalibrationTargetVariance
import ProphetSecretary.Statistics.CalibrationTargetComparison
import ProphetSecretary.Statistics.CalibrationMaximumErrors
import ProphetSecretary.Statistics.EmpiricalCoarseValue
import ProphetSecretary.Model.HalfGuarantee
import ProphetSecretary.Statistics.CalibrationCountCutoff
import ProphetSecretary.Statistics.CalibrationQueryFailure

/-!
# Accuracy of the implemented duration target

A deterministic true-law ratio minimizer supplies a grid candidate. Its
sampling numerator separates a frozen optimal-policy kernel from empirical
adaptation. The empirical count and maximum guards are charged as exceptional
events. Paper: `lem:calibration-target`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m : ℕ} [NeZero m]

/-- A ratio below the target ceiling has a deterministic minimizing duration coefficient in `[0,4]`. -/
lemma exists_duration_ratio_minimizer (P : Instance n) (hP : P.HasPositiveFiniteMaximum)
    (hM : P.expectedMaximum ≤ 1) (hGamma : P.optimalScalarRatio < (4/5 : ℝ)) :
    ∃ lam z : ℝ, lam ∈ Ioc (0 : ℝ) 1 ∧ z ∈ Icc (0 : ℝ) 4 ∧
      1/(1+z)=lam ∧ P.optimalScalarRatio=P.normalizedScalarRatio lam ∧
      P.optimalScalarRatio=P.durationScalarRatio z := by
  obtain ⟨lam, hlam, hmin, _⟩ := P.exists_scalarRatio_minimizer hP
  have hl : 0 < lam := by
    by_contra hn
    have hz : lam = 0 := le_antisymm (le_of_not_gt hn) hlam.1
    rw [hz, P.normalizedScalarRatio_zero] at hmin
    linarith
  let z := (1-lam)/lam
  have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr hlam.2) hl.le
  have he : 1/(1+z)=lam := by dsimp [z]; field_simp; ring
  have hEq := P.normalizedScalarRatio_eq_durationScalarRatio hP hz
  rw [he] at hEq
  have hRatio : P.optimalScalarRatio=P.durationScalarRatio z := hmin.trans hEq
  have hzM : z < 4*P.expectedMaximum := by
    by_contra hn
    have h := P.durationScalarRatio_ge_fourFifths hP (le_of_not_gt hn)
    rw [← hRatio] at h
    linarith
  refine ⟨lam, z, ⟨hl, hlam.2⟩, ⟨hz, by linarith⟩, he, hmin, hRatio⟩

private lemma clipped_target_positive_error_le {r gamma : ℝ} (hgamma : (1/2 : ℝ) ≤ gamma) :
    max 0 (min (4/5) (max (1/2) r)-gamma) ≤ max 0 (r-gamma) := by
  have h0 : 0 ≤ max 0 (r-gamma) := le_max_left _ _
  have hR : r ≤ gamma+max 0 (r-gamma) := by linarith [le_max_right (0 : ℝ) (r-gamma)]
  have hC : min (4/5) (max (1/2) r) ≤ gamma+max 0 (r-gamma) :=
    (min_le_right _ _).trans (max_le (by linarith) hR)
  exact max_le h0 (by linarith)

lemma numericalTarget_positive_error_le_minimum (mu : ℝ)
    (y : (Fin n × Fin m) → ℝ) (v : TargetGrid m → ℝ)
    (hEligible : targetEligible mu y) {gamma : ℝ} (hgamma : (1/2 : ℝ) ≤ gamma) :
    max 0 (numericalTarget mu y v-gamma) ≤ max 0 (targetMinimumRatio y v-gamma) := by
  have hg : ¬(targetCountCutoff m < empiricalPositiveCount y ∨ trainingExpectedMaximum y < mu/2) :=
    fun h => h.elim (not_lt_of_ge hEligible.1) (not_lt_of_ge hEligible.2)
  rw [numericalTarget, if_neg hg]
  exact clipped_target_positive_error_le hgamma

/-- On eligible accurate data the target's upward error is controlled by one fixed value estimate. -/
lemma numericalTarget_coarse_pointwise (P : Instance n) (hP : P.HasPositiveFiniteMaximum)
    (mu : ℝ) (hmu : 0 < mu) (y : (Fin n × Fin m) → ℝ) (v : TargetGrid m → ℝ)
    (hEligible : targetEligible mu y) (hGood : ¬queryFailure mu y v)
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 4)
    (hRatio : P.optimalScalarRatio=P.durationScalarRatio z) :
    max 0 (numericalTarget mu y v-P.optimalScalarRatio) ≤
      (2/mu)*(|optimalScalarValue (trainingInstance y) 1 z-optimalScalarValue P 1 z|+
        |trainingExpectedMaximum y-P.expectedMaximum|)+6/(mu*(m : ℝ)) := by
  have hGamma := P.optimalScalarRatio_bounds hP
  have hHalf : (1/2 : ℝ) ≤ P.optimalScalarRatio := half_le_optimalCompetitiveRatio.trans hGamma.1
  have hG0 : 0 ≤ P.optimalScalarRatio := le_trans (by norm_num) hHalf
  have hMean : 0 < trainingExpectedMaximum y := by linarith [hEligible.2]
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hAcc : ∀ j, v j ≤ optimalScalarValue (trainingInstance y) 1 (targetGrid j)+1/(m : ℝ) := by
    intro j
    have hAll : ∀ j, |v j-optimalScalarValue (trainingInstance y) 1 (targetGrid j)| ≤ 1/(m : ℝ) := by
      by_contra hn
      exact hGood ⟨hEligible, hn⟩
    linarith [(abs_le.mp (hAll j)).2]
  have hMin := targetMinimumRatio_le_at y v hMean hz hAcc
  have hClip := numericalTarget_positive_error_le_minimum mu y v hEligible hHalf
  let A := |optimalScalarValue (trainingInstance y) 1 z-optimalScalarValue P 1 z|+
    |trainingExpectedMaximum y-P.expectedMaximum|
  have hA : 0 ≤ A := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hDP : 0 < P.expectedMaximum+z := add_pos_of_pos_of_nonneg hP.2 hz.1
  have hDQ : 0 < trainingExpectedMaximum y+z := add_pos_of_pos_of_nonneg hMean hz.1
  have hTrue : P.optimalScalarRatio*(P.expectedMaximum+z) = optimalScalarValue P 1 z := by
    apply (eq_div_iff hDP.ne').mp
    exact hRatio
  have hN : optimalScalarValue (trainingInstance y) 1 z-
      P.optimalScalarRatio*(trainingExpectedMaximum y+z) ≤ A := by
    have hOne := mul_le_mul_of_nonneg_left (neg_le_abs (trainingExpectedMaximum y-P.expectedMaximum)) hG0
    have hTwo := mul_le_mul_of_nonneg_right hGamma.2 (abs_nonneg (trainingExpectedMaximum y-P.expectedMaximum))
    have hVal := le_abs_self (optimalScalarValue (trainingInstance y) 1 z-optimalScalarValue P 1 z)
    dsimp [A]
    nlinarith
  have hE : (trainingInstance y).durationScalarRatio z-P.optimalScalarRatio ≤ A/(trainingExpectedMaximum y+z) := by
    have h := div_le_div_of_nonneg_right hN hDQ.le
    have he : (trainingInstance y).durationScalarRatio z-P.optimalScalarRatio =
        (optimalScalarValue (trainingInstance y) 1 z-P.optimalScalarRatio*(trainingExpectedMaximum y+z))/
          (trainingExpectedMaximum y+z) := by
      change optimalScalarValue (trainingInstance y) 1 z/(trainingExpectedMaximum y+z)-P.optimalScalarRatio = _
      field_simp [hDQ.ne']
    rw [he]
    exact h
  have hBound : A/(trainingExpectedMaximum y+z) ≤ (2/mu)*A := by
    have hDen : mu/2 ≤ trainingExpectedMaximum y+z := by linarith [hEligible.2, hz.1]
    have h := div_le_div_of_nonneg_left hA (div_pos hmu (by norm_num : (0 : ℝ)<2)) hDen
    apply h.trans_eq
    field_simp
  have hPrec : 3/((m : ℝ)*trainingExpectedMaximum y) ≤ 6/(mu*(m : ℝ)) := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤3)
      (mul_pos hm (div_pos hmu (by norm_num : (0 : ℝ)<2)))
      (mul_le_mul_of_nonneg_left hEligible.2 hm.le)
    apply h.trans_eq
    field_simp
    ring
  have hRaw : targetMinimumRatio y v-P.optimalScalarRatio ≤ (2/mu)*A+6/(mu*(m : ℝ)) := by
    linarith [hMin, hE, hBound, hPrec]
  have hNonneg : 0 ≤ (2/mu)*A+6/(mu*(m : ℝ)) := by positivity
  exact hClip.trans (max_le hNonneg hRaw)

lemma target_error_integral_le_of_pointwise {Seed : Type*} [MeasurableSpace Seed]
    (P : Instance n) (hP : P.HasPositiveFiniteMaximum) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (mu : ℝ) (out : (((Fin n × Fin m) → ℝ) × Seed) → TargetGrid m → ℝ) (ho : Measurable out)
    (A : ((Fin n × Fin m) → ℝ) → ℝ) (hAI : Integrable A (P.trainingCoordinateLaw m))
    (hA0 : ∀ a, 0 ≤ A a)
    (hPoint : ∀ᵐ p ∂(P.trainingCoordinateLaw m).prod ν,
      targetEligible mu p.1 → ¬queryFailure mu p.1 (out p) →
      max 0 (numericalTarget mu p.1 (out p)-P.optimalScalarRatio) ≤ A p.1) :
    (∫ p, max 0 (numericalTarget mu p.1 (out p)-P.optimalScalarRatio)
      ∂(P.trainingCoordinateLaw m).prod ν) ≤
      (∫ a, A a ∂P.trainingCoordinateLaw m) +
      (P.trainingCoordinateLaw m).real {a | targetCountCutoff m < empiricalPositiveCount a} +
      (P.trainingCoordinateLaw m).real {a | trainingExpectedMaximum a < mu/2} +
      ((P.trainingCoordinateLaw m).prod ν).real {p | queryFailure mu p.1 (out p)} := by
  let Ω := (((Fin n × Fin m) → ℝ) × Seed)
  let μ : Measure Ω := (P.trainingCoordinateLaw m).prod ν
  let T : Ω → ℝ := fun p => max 0 (numericalTarget mu p.1 (out p)-P.optimalScalarRatio)
  let ECount : Set Ω := {p | targetCountCutoff m < empiricalPositiveCount p.1}
  let EMean : Set Ω := {p | trainingExpectedMaximum p.1 < mu/2}
  let EQuery : Set Ω := {p | queryFailure mu p.1 (out p)}
  have hCm : MeasurableSet ECount := measurableSet_lt measurable_const
    (measurable_empiricalPositiveCount.comp measurable_fst)
  have hMm : MeasurableSet EMean := measurableSet_lt
    (measurable_trainingExpectedMaximum.comp measurable_fst) measurable_const
  have hQm : MeasurableSet EQuery := (measurableSet_queryFailure mu).preimage (measurable_fst.prodMk ho)
  have hG0 : 0 ≤ P.optimalScalarRatio := optimalCompetitiveRatio_nonnegative.trans (P.optimalScalarRatio_bounds hP).1
  have hT1 (p : Ω) : T p ≤ 1 := by
    apply max_le (by norm_num)
    have h := (numericalTarget_range mu p.1 (out p)).2
    linarith
  have hTI : Integrable T μ := by
    apply Integrable.of_bound
      (measurable_const.max (((measurable_numericalTarget mu).comp
        (measurable_fst.prodMk ho)).sub_const P.optimalScalarRatio)).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun p => by
      change ‖T p‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact hT1 p
  have hCI : Integrable (ECount.indicator (fun _ : Ω => (1 : ℝ))) μ := (integrable_const 1).indicator hCm
  have hMI : Integrable (EMean.indicator (fun _ : Ω => (1 : ℝ))) μ := (integrable_const 1).indicator hMm
  have hQI : Integrable (EQuery.indicator (fun _ : Ω => (1 : ℝ))) μ := (integrable_const 1).indicator hQm
  have hAProd : Integrable (fun p : Ω => A p.1) μ :=
    (measurePreserving_fst : MeasurePreserving (Prod.fst : Ω → _) μ (P.trainingCoordinateLaw m)).integrable_comp_of_integrable hAI
  have hInd0 (E : Set Ω) (p : Ω) : 0 ≤ E.indicator (fun _ : Ω => (1 : ℝ)) p := by
    by_cases h : p ∈ E <;> simp [h]
  have hI := integral_mono_ae hTI (((hAProd.add hCI).add hMI).add hQI) (by
    filter_upwards [hPoint] with p hp
    change T p ≤ A p.1+ECount.indicator (fun _ : Ω => (1 : ℝ)) p+
      EMean.indicator (fun _ : Ω => (1 : ℝ)) p+EQuery.indicator (fun _ : Ω => (1 : ℝ)) p
    by_cases hC : p ∈ ECount
    · rw [Set.indicator_of_mem hC]
      linarith [hT1 p, hA0 p.1, hInd0 EMean p, hInd0 EQuery p]
    · by_cases hM : p ∈ EMean
      · rw [Set.indicator_of_notMem hC, Set.indicator_of_mem hM]
        linarith [hT1 p, hA0 p.1, hInd0 EQuery p]
      · by_cases hQ : p ∈ EQuery
        · rw [Set.indicator_of_notMem hC, Set.indicator_of_notMem hM, Set.indicator_of_mem hQ]
          linarith [hT1 p, hA0 p.1]
        · rw [Set.indicator_of_notMem hC, Set.indicator_of_notMem hM, Set.indicator_of_notMem hQ]
          simp only [add_zero]
          exact hp ⟨le_of_not_gt hC, le_of_not_gt hM⟩ hQ)
  change (∫ p, T p ∂μ) ≤ ∫ p,
    A p.1+ECount.indicator (fun _ : Ω => (1 : ℝ)) p+
      EMean.indicator (fun _ : Ω => (1 : ℝ)) p+EQuery.indicator (fun _ : Ω => (1 : ℝ)) p ∂μ at hI
  rw [integral_add (f := fun p => A p.1+ECount.indicator (fun _ : Ω => (1 : ℝ)) p+
      EMean.indicator (fun _ : Ω => (1 : ℝ)) p) (g := EQuery.indicator (fun _ : Ω => (1 : ℝ)))
      ((hAProd.add hCI).add hMI) hQI,
    integral_add (f := fun p => A p.1+ECount.indicator (fun _ : Ω => (1 : ℝ)) p)
      (g := EMean.indicator (fun _ : Ω => (1 : ℝ))) (hAProd.add hCI) hMI,
    integral_add (f := fun p => A p.1) (g := ECount.indicator (fun _ : Ω => (1 : ℝ))) hAProd hCI,
    integral_indicator_const (1 : ℝ) hCm, integral_indicator_const (1 : ℝ) hMm,
    integral_indicator_const (1 : ℝ) hQm, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    mul_one, mul_one, mul_one, integral_fun_fst, probReal_univ, one_smul] at hI
  have hCount : μ.real ECount = (P.trainingCoordinateLaw m).real
      {a | targetCountCutoff m < empiricalPositiveCount a} := by
    have h := (measurePreserving_fst : MeasurePreserving (Prod.fst : Ω → _) μ (P.trainingCoordinateLaw m))
    have hm : MeasurableSet {a : (Fin n × Fin m) → ℝ | targetCountCutoff m < empiricalPositiveCount a} :=
      measurableSet_lt measurable_const measurable_empiricalPositiveCount
    exact (map_measureReal_apply h.measurable hm).symm.trans (by rw [h.map_eq])
  have hMean : μ.real EMean = (P.trainingCoordinateLaw m).real
      {a | trainingExpectedMaximum a < mu/2} := by
    have h := (measurePreserving_fst : MeasurePreserving (Prod.fst : Ω → _) μ (P.trainingCoordinateLaw m))
    have hm : MeasurableSet {a : (Fin n × Fin m) → ℝ | trainingExpectedMaximum a < mu/2} :=
      measurableSet_lt measurable_trainingExpectedMaximum measurable_const
    exact (map_measureReal_apply h.measurable hm).symm.trans (by rw [h.map_eq])
  rw [hCount, hMean] at hI
  exact hI

/-- Expected upward error of the actual finite target, before bounding the three exceptional probabilities. -/
theorem numericalTarget_expected_coarse_components {Seed : Type*} [MeasurableSpace Seed]
    (P : Instance n) (hP : P.HasPositiveFiniteMaximum)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (mu : ℝ) (hmu : 0 < mu)
    (out : (((Fin n × Fin m) → ℝ) × Seed) → TargetGrid m → ℝ) (ho : Measurable out)
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 4)
    (hRatio : P.optimalScalarRatio=P.durationScalarRatio z) :
    (∫ p, max 0 (numericalTarget mu p.1 (out p)-P.optimalScalarRatio)
      ∂(P.trainingCoordinateLaw m).prod ν) ≤
      (2/mu)*(4/Real.sqrt (m : ℝ)+Real.sqrt (P.expectedMaximum/(m : ℝ))) +
      6/(mu*(m : ℝ)) +
      (P.trainingCoordinateLaw m).real {a | targetCountCutoff m < empiricalPositiveCount a} +
      (P.trainingCoordinateLaw m).real {a | trainingExpectedMaximum a < mu/2} +
      ((P.trainingCoordinateLaw m).prod ν).real {p | queryFailure mu p.1 (out p)} := by
  let fV : ((Fin n × Fin m) → ℝ) → ℝ := fun a =>
    |optimalScalarValue (trainingInstance a) 1 z-optimalScalarValue P 1 z|
  let fM : ((Fin n × Fin m) → ℝ) → ℝ := fun a => |trainingExpectedMaximum a-P.expectedMaximum|
  let A : ((Fin n × Fin m) → ℝ) → ℝ := fun a => (2/mu)*(fV a+fM a)+6/(mu*(m : ℝ))
  have hVI : Integrable fV (P.trainingCoordinateLaw m) :=
    ((integrable_empiricalScalarValue_unit (k := m) P hcap hz.1).sub (integrable_const _)).abs
  have hMI : Integrable fM (P.trainingCoordinateLaw m) :=
    (((P.memLp_empiricalExpectedMaximum (k := m) 1 hcap 2).integrable (by norm_num)).sub (integrable_const _)).abs
  have hAI : Integrable A (P.trainingCoordinateLaw m) :=
    ((hVI.add hMI).const_mul (2/mu)).add (integrable_const _)
  have hA0 (a) : 0 ≤ A a := by dsimp [A, fV, fM]; positivity
  have h := target_error_integral_le_of_pointwise P hP ν mu out ho A hAI hA0
    (Filter.Eventually.of_forall fun p hEligible hGood =>
      numericalTarget_coarse_pointwise P hP mu hmu p.1 (out p) hEligible hGood hz hRatio)
  have heA : (∫ a, A a ∂P.trainingCoordinateLaw m) =
      (2/mu)*((∫ a, fV a ∂P.trainingCoordinateLaw m)+(∫ a, fM a ∂P.trainingCoordinateLaw m))+
      6/(mu*(m : ℝ)) := by
    change (∫ a, (2/mu)*(fV a+fM a)+6/(mu*(m : ℝ)) ∂P.trainingCoordinateLaw m) = _
    rw [integral_add (f := fun a => (2/mu)*(fV a+fM a))
        (g := fun _ => 6/(mu*(m : ℝ))) ((hVI.add hMI).const_mul (2/mu)) (integrable_const _),
      integral_const_mul, integral_add (f := fV) (g := fM) hVI hMI,
      integral_const, probReal_univ, one_smul]
  have hV := P.empiricalScalarValue_L1_error_le (k := m) hcap hz.1
  have hM := P.empiricalMaximum_L1_error_le (k := m) hcap
  have hStat := mul_le_mul_of_nonneg_left (add_le_add hV hM) (by positivity : (0 : ℝ) ≤ 2/mu)
  change (2/mu)*((∫ a, fV a ∂P.trainingCoordinateLaw m)+(∫ a, fM a ∂P.trainingCoordinateLaw m)) ≤
    (2/mu)*(4/Real.sqrt (m : ℝ)+Real.sqrt (P.expectedMaximum/(m : ℝ))) at hStat
  rw [heA] at h
  linarith

private lemma sample_inverse_bounds :
    1/(m : ℝ) ≤ 1/Real.sqrt (m : ℝ) ∧
    1/(m : ℝ)^2 ≤ 1/Real.sqrt (m : ℝ) ∧
    Real.exp (-2*(m : ℝ)) ≤ 1/Real.sqrt (m : ℝ) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm
  have hInv : 1/(m : ℝ) ≤ 1/Real.sqrt (m : ℝ) :=
    one_div_le_one_div_of_le hs (Real.sqrt_le_self_iff.mpr (Or.inr hm1))
  refine ⟨hInv, ?_, ?_⟩
  · exact (one_div_le_one_div_of_le hm (by nlinarith : (m : ℝ) ≤ (m : ℝ)^2)).trans hInv
  · have hExp : (m : ℝ) ≤ Real.exp (2*(m : ℝ)) := by
      linarith [Real.add_one_le_exp (2*(m : ℝ))]
    calc
      Real.exp (-2*(m : ℝ)) = 1/Real.exp (2*(m : ℝ)) := by
        simp only [neg_mul, Real.exp_neg, one_div]
      _ ≤ 1/(m : ℝ) := one_div_le_one_div_of_le hm hExp
      _ ≤ _ := hInv

/-- The implemented finite target has the coarse inverse-square-root error bound. -/
theorem numericalTarget_expected_coarse {Seed : Type*} [MeasurableSpace Seed]
    (P : Instance n) (hP : P.HasPositiveFiniteMaximum)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (mu : ℝ) (hmu : 0 < mu)
    (hMean : mu ≤ P.expectedMaximum) (hCount : P.positiveCount ≤ 2*Real.log (m : ℝ))
    (out : (((Fin n × Fin m) → ℝ) × Seed) → TargetGrid m → ℝ) (ho : Measurable out)
    (hConf : ∀ᵐ a ∂P.trainingCoordinateLaw m, targetEligible mu a → ∀ j : TargetGrid m,
      ν.real {r | 1/(m : ℝ) < |out (a,r) j-optimalScalarValue (trainingInstance a) 1 (targetGrid j)|} ≤
        1/((m : ℝ)^2*(4*(m : ℝ)+1))) :
    (∫ p, max 0 (numericalTarget mu p.1 (out p)-P.optimalScalarRatio)
      ∂(P.trainingCoordinateLaw m).prod ν) ≤ (20/mu+2)/Real.sqrt (m : ℝ) := by
  by_cases hHigh : (4/5 : ℝ) ≤ P.optimalScalarRatio
  · have hz (p : (((Fin n × Fin m) → ℝ) × Seed)) :
        max 0 (numericalTarget mu p.1 (out p)-P.optimalScalarRatio) = 0 :=
      max_eq_left (sub_nonpos.mpr ((numericalTarget_range mu p.1 (out p)).2.trans hHigh))
    simp_rw [hz, integral_zero]
    positivity
  · have hM1 := P.expectedMaximum_le_of_bounded zero_le_one hcap
    obtain ⟨lam, z, _, hz, _, _, hRatio⟩ :=
      exists_duration_ratio_minimizer P hP hM1 (lt_of_not_ge hHigh)
    have hComp := numericalTarget_expected_coarse_components P hP hcap ν mu hmu out ho hz hRatio
    have hCountBound := empiricalPositiveCount_cutoff_probability (m := m) P hCount
    have hMeanBound := P.empiricalMaximum_small_probability (k := m) hcap hmu hMean
    change (P.trainingCoordinateLaw m).real {a | trainingExpectedMaximum a < mu/2} ≤
      4/(mu*(m : ℝ)) at hMeanBound
    have hQueryBound := queryFailure_probability_le (P.trainingCoordinateLaw m) ν mu out ho hConf
    have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
    have hRoot : Real.sqrt (P.expectedMaximum/(m : ℝ)) ≤ 1/Real.sqrt (m : ℝ) := by
      calc
        _ ≤ Real.sqrt (1/(m : ℝ)) := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hM1 hm.le)
        _ = _ := by rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
    obtain ⟨hInv, hInv2, hExp⟩ := sample_inverse_bounds (m := m)
    have hBase := mul_le_mul_of_nonneg_left (add_le_add (le_refl (4/Real.sqrt (m : ℝ))) hRoot)
      (by positivity : (0 : ℝ) ≤ 2/mu)
    have hPrecision : 6/(mu*(m : ℝ)) ≤ (6/mu)*(1/Real.sqrt (m : ℝ)) := by
      calc
        _ = (6/mu)*(1/(m : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hInv (by positivity)
    have hMeanBound' : (P.trainingCoordinateLaw m).real {a | trainingExpectedMaximum a < mu/2} ≤
        (4/mu)*(1/Real.sqrt (m : ℝ)) :=
      hMeanBound.trans (by
        calc
          4/(mu*(m : ℝ)) = (4/mu)*(1/(m : ℝ)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hInv (by positivity))
    have hAll := add_le_add (add_le_add (add_le_add (add_le_add hBase hPrecision)
      (hCountBound.trans hExp)) hMeanBound') (hQueryBound.trans hInv2)
    exact hComp.trans (hAll.trans_eq (by ring))

end ProphetSecretary.Statistics.Calibration
