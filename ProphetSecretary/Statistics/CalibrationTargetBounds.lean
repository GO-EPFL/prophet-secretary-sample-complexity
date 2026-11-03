import ProphetSecretary.Statistics.CalibrationTargetNearCritical
import ProphetSecretary.Model.SmallMeanClamp

/-!
# Uniform sharp accuracy of the calibrated numerical target

Endpoint slack places a small-gap ratio minimizer in one fixed interior
interval. The sharp estimate there and the coarse estimate for larger gaps
give one constant before the instance size, sample count and unknown laws.
Conditional numerical confidence remains an explicit input, discharged by
the scalar planner when the target is used in the learner.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

/-- Waiting gives the explicit left-endpoint slack used in the calibrated construction. -/
lemma calibration_gap_left_slack {n : ℕ} (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (hSmall : P.expectedMaximum ≤ 1/80)
    {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) (4/5)) :
    17/400 ≤ normalizedScalarGap P lam := by
  have hP := P.integrable_maximum_of_bounded hcap
  have hTime : 0 ≤ 1-lam := by linarith [hlam.2]
  have hWait := durationWeight_le_optimalScalarValue P hP hlam.1 hTime
  have hC := optimalCompetitiveRatio_le_threeQuarters
  have hCM : optimalCompetitiveRatio*P.expectedMaximum ≤ 3/320 := by
    have h := mul_le_mul hC hSmall P.expectedMaximum_nonnegative (by norm_num : (0 : ℝ)≤3/4)
    norm_num at h
    exact h
  have hCw := mul_le_mul_of_nonneg_right hC hTime
  have hCMw := mul_le_mul_of_nonneg_left hCM hlam.1
  unfold normalizedScalarGap scalarGap
  nlinarith only [hWait, hCw, hCMw, hlam.2]

/-- The sharp target error rate of `lem:calibration-target`, uniformly over
all numerical tables satisfying the prescribed single-query confidence. -/
theorem exists_numericalTarget_sharp_bound (mu : ℝ) (hmu : 0 < mu) (_hmuHi : mu < 1/80)
    (S0 : ℝ) (hS0 : 0 ≤ S0) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n m : ℕ) [NeZero m] (P : Instance n)
      (_hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1)
      (_hMean : mu ≤ P.expectedMaximum) (_hSmall : P.expectedMaximum ≤ 1/80)
      (_hCount : P.positiveCount ≤ 2*Real.log (m : ℝ)) (_hS : P.totalFirstMoment ≤ S0)
      (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
      (out : (((Fin n × Fin m) → ℝ) × Seed) → TargetGrid m → ℝ) (_ho : Measurable out),
      (∀ᵐ a ∂P.trainingCoordinateLaw m, targetEligible mu a → ∀ j : TargetGrid m,
        ν.real {r | 1/(m : ℝ) < |out (a,r) j-optimalScalarValue (trainingInstance a) 1 (targetGrid j)|} ≤
          1/((m : ℝ)^2*(4*(m : ℝ)+1))) →
      (∫ p, max 0 (numericalTarget mu p.1 (out p)-P.optimalScalarRatio)
        ∂(P.trainingCoordinateLaw m).prod ν) ≤
        K*Real.sqrt ((P.optimalScalarRatio-optimalCompetitiveRatio)/(m : ℝ))+K/(m : ℝ) := by
  obtain ⟨b, d, hb, hd, hSlack⟩ := bounded_smallMean_clamp_with_slack mu hmu
  let δ := 1-b
  have hδ : 0 < δ := by dsimp [δ]; linarith [hb.2]
  have hδOne : δ ≤ 1 := by dsimp [δ]; linarith [hb.1]
  have hδHi : δ ≤ 1/δ := by
    apply (le_div_iff₀ hδ).mpr
    have h := pow_le_pow_left₀ hδ.le hδOne 2
    nlinarith
  let A := (2/mu)*(Real.sqrt (pilotFirstProjectionConstant δ*(1+S0))+1)
  let B := (2/mu)*(1+empiricalCandidateRegretConstant δ (1/δ)*S0*(1+S0))+10/mu+2
  let C := 20/mu+2
  let K := A+B+C/Real.sqrt d+1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by
    have hR := (empiricalCandidateRegretConstant_positive hδ hδHi).le
    dsimp [B]
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCd : 0 ≤ C/Real.sqrt d := by positivity
  have hK : 0 < K := by dsimp [K]; linarith
  have hKA : A ≤ K := by dsimp [K]; linarith
  have hKB : B ≤ K := by dsimp [K]; linarith
  have hKC : C/Real.sqrt d ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro n m hm P hcap hMean hSmall hCount hS Seed inst ν instν out ho hConf
  have hP : P.HasPositiveFiniteMaximum := ⟨P.integrable_maximum_of_bounded hcap, hmu.trans_le hMean⟩
  let g := P.optimalScalarRatio-optimalCompetitiveRatio
  have hg : 0 ≤ g := sub_nonneg.mpr (P.optimalScalarRatio_bounds hP).1
  have hmPos : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hRootD : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hRootM : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmPos
  by_cases hLarge : d ≤ g
  · have hCoarse := numericalTarget_expected_coarse P hP hcap ν mu hmu hMean hCount out ho hConf
    have hOrder := Real.sqrt_le_sqrt hLarge
    have hMult := mul_le_mul_of_nonneg_left hOrder hCd
    calc
      _ ≤ C/Real.sqrt (m : ℝ) := hCoarse
      _ = ((C/Real.sqrt d)*Real.sqrt d)/Real.sqrt (m : ℝ) := by rw [div_mul_cancel₀ _ hRootD.ne']
      _ ≤ ((C/Real.sqrt d)*Real.sqrt g)/Real.sqrt (m : ℝ) :=
        div_le_div_of_nonneg_right hMult hRootM.le
      _ = (C/Real.sqrt d)*Real.sqrt (g/(m : ℝ)) := by rw [Real.sqrt_div hg]; ring
      _ ≤ K*Real.sqrt (g/(m : ℝ)) := mul_le_mul_of_nonneg_right hKC (Real.sqrt_nonneg _)
      _ ≤ K*Real.sqrt (g/(m : ℝ))+K/(m : ℝ) := le_add_of_nonneg_right (div_nonneg hK.le hmPos.le)
  · have hSmallGap : g < d := lt_of_not_ge hLarge
    obtain ⟨lam, hlam, hmin, _⟩ := P.exists_scalarRatio_minimizer hP
    have hM1 := P.expectedMaximum_le_of_bounded zero_le_one hcap
    have hDen : lam*P.expectedMaximum+1-lam ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hM1 hlam.1
      linarith
    have hGap : normalizedScalarGap P lam ≤ g := by
      rw [P.normalizedScalarGap_at_ratio_minimizer hP hlam hmin]
      have h := mul_le_mul_of_nonneg_left hDen hg
      simpa only [mul_one] using h
    have hIn : lam ∈ Icc (4/5 : ℝ) b := by
      by_contra hn
      have h := (hSlack n P hcap hMean hSmall).1 lam hlam hn
      linarith
    have hLamδ : lam ∈ Icc δ (1-δ) := by
      constructor <;> dsimp [δ] <;> linarith [hIn.1, hIn.2, hb.1]
    have hLam : lam ∈ Ioc (0 : ℝ) 1 := ⟨hδ.trans_le hLamδ.1, hlam.2⟩
    have hZ : (1-lam)/lam ∈ Icc δ (1/δ) := by
      constructor
      · apply (le_div_iff₀ hLam.1).mpr
        have h := mul_le_mul_of_nonneg_left hlam.2 hδ.le
        linarith [hLamδ.2]
      · calc
          _ ≤ 1/lam := div_le_div_of_nonneg_right (by linarith [hlam.1]) hLam.1.le
          _ ≤ 1/δ := one_div_le_one_div_of_le hδ hLamδ.1
    let π := P.valuePolicy hP.1 hLam.1.le (sub_nonneg.mpr hlam.2)
    have hOpt : π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam) :=
      P.valuePolicy_optimal hP.1 hLam.1 (sub_nonneg.mpr hlam.2)
    have hSharp := numericalTarget_expected_sharp_on_interior π P hP hcap ν mu hmu hMean hCount out ho hConf
      hδ hLamδ hIn.1 hδ hδHi hZ hS0 hS hmin hOpt
    have hACompare := mul_le_mul_of_nonneg_right hKA (Real.sqrt_nonneg (g/(m : ℝ)))
    have hBCompare := div_le_div_of_nonneg_right hKB hmPos.le
    exact hSharp.trans (add_le_add hACompare hBCompare)

end ProphetSecretary.Statistics.Calibration
