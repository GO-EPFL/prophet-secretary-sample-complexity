import ProphetSecretary.Statistics.FairCalibratedLearner
import ProphetSecretary.Statistics.FiniteRankCalibrationGuarantee
import ProphetSecretary.Statistics.CalibratedOuter.FairReduction

/-!
# The finite-bit statistical guarantee

The validation keys and mixture coin add a bounded-instance error of
order (1/m^2). The independent outer marks add a separate loss measured
relative to the original expected maximum.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m : ℕ}

namespace FairCalibrationParameters

def coinBits (_ : FairCalibrationParameters n m) : ℕ := Nat.clog 2 (m^2)

noncomputable def finiteLearner (a : FairCalibrationParameters n m) (mu : ℝ) : RankLearner n (2*m) :=
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  finiteRankCalibratedLearner (J := a.grid) a.clockBits a.coinBits a.targetLaw a.thresholdLaw
    mu a.zlo (1/4) a.target a.threshold a.measurable_target a.measurable_threshold

lemma finiteExecution_error_le (a : FairCalibrationParameters n m) :
    (m : ℝ)*((n : ℝ)*((n : ℝ)-1))/(2*((2^a.clockBits : ℕ) : ℝ))+
      1/((2^a.coinBits : ℕ) : ℝ) ≤ 2/(m : ℝ) := by
  have hm : (1 : ℝ) ≤ m := by
    exact_mod_cast (show 1≤m by have := a.two_le; omega)
  have hm0 : (0 : ℝ)<m := zero_lt_one.trans_le hm
  let N := ((2^a.clockBits : ℕ) : ℝ)
  let Q := ((2^a.coinBits : ℕ) : ℝ)
  have hN : 0<N := by dsimp [N]; positivity
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hc : (m : ℝ)^3*(n : ℝ)^2≤N := by
    dsimp only [N]
    exact_mod_cast calibrationClockGrid_validation n m a.clockInverse
  have hq : (m : ℝ)^2≤Q := by
    dsimp only [Q]
    exact_mod_cast (Nat.le_pow_clog (by decide : 1<2) (m^2))
  have hKeys : (m : ℝ)*((n : ℝ)*((n : ℝ)-1))/(2*N)≤1/(2*(m : ℝ)^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hnn : (n : ℝ)*((n : ℝ)-1)≤(n : ℝ)^2 := by
      nlinarith only [Nat.cast_nonneg (α := ℝ) n]
    calc
      _ = (2*(m : ℝ)^3)*((n : ℝ)*((n : ℝ)-1)) := by ring
      _ ≤ (2*(m : ℝ)^3)*(n : ℝ)^2 := mul_le_mul_of_nonneg_left hnn (by positivity)
      _ = 2*((m : ℝ)^3*(n : ℝ)^2) := by ring
      _ ≤ 1*(2*N) := by linarith only [hc]
  have hCoin : 1/Q≤1/(m : ℝ)^2 := (one_div_le_one_div hQ (by positivity)).mpr hq
  have hM : (m : ℝ)≤(m : ℝ)^2 := by nlinarith only [hm, sq_nonneg ((m : ℝ)-1)]
  change (m : ℝ)*((n : ℝ)*((n : ℝ)-1))/(2*N)+1/Q≤_
  calc
    _ ≤ 1/(2*(m : ℝ)^2)+1/(m : ℝ)^2 := add_le_add hKeys hCoin
    _ ≤ 2/(m : ℝ)^2 := by
      have hh := (one_div_le_one_div (by positivity : 0<2*(m : ℝ)^2) (by positivity : 0<(m : ℝ)^2)).mpr
        (by nlinarith : (m : ℝ)^2≤2*(m : ℝ)^2)
      linarith only [hh,show (2 : ℝ)/(m : ℝ)^2=1/(m : ℝ)^2+1/(m : ℝ)^2 by ring]
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hm0 hM

theorem finiteLearner_transfer (a : FairCalibrationParameters n m) (mu : ℝ) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) :
    (a.reportedLearner mu).expectedReward P-2/(m : ℝ)≤(a.finiteLearner mu).expectedReward P ∧
      ∀ i, (a.reportedLearner mu).reachProbability P i-2/(m : ℝ)≤
        (a.finiteLearner mu).reachProbability P i := by
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  have h := finiteRankCalibratedLearner_transfer (J := a.grid) P hcap a.clockBits a.coinBits
    a.targetLaw a.thresholdLaw mu a.coefficient_mem.1.le a.coefficient_mem.2.le a.target a.threshold
    a.measurable_target a.measurable_threshold
  exact ⟨(sub_le_sub_left a.finiteExecution_error_le _).trans h.1,
    fun i => (sub_le_sub_left a.finiteExecution_error_le _).trans (h.2 i)⟩

end FairCalibrationParameters

/-- Bounded reward and reach with the fair-bit scalar queries, actual
validation keys, sorted dyadic clocks, and the finite mixture coin. -/
theorem exists_finite_rank_calibrated_learner (mu : ℝ) (hmu : 0<mu) (hmuHi : mu<1/80) :
    ∃ (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (zInv : ℕ)
      (hInv : 1/((1-(b : ℝ))/(b : ℝ))≤(zInv : ℝ)) (K : ℝ), 0<K ∧
      ∀ (n m : ℕ) (hn : 0<n) (hm : 2≤m) (P : Instance n),
        (∀ i, ∀ᵐ x ∂P.law i, x≤1) → mu≤P.expectedMaximum → P.expectedMaximum≤1/80 →
        P.positiveCount≤2*Real.log (m : ℝ) →
        let a : FairCalibrationParameters n m :=
          ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
        let L := a.finiteLearner mu
        optimalCompetitiveRatio*P.expectedMaximum-K/(m : ℝ)≤L.expectedReward P ∧
        ∀ i, optimalCompetitiveRatio-K/(m : ℝ)≤L.reachProbability P i := by
  obtain ⟨b,hb,zInv,hInv,K,hK,hReported⟩ := exists_fair_reported_learner mu hmu hmuHi
  refine ⟨b,hb,zInv,hInv,K+2,by linarith,?_⟩
  intro n m hn hm P hcap hM hSmall hL
  dsimp only
  let a : FairCalibrationParameters n m :=
    ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
  have hr := hReported n m hn hm P hcap hM hSmall hL
  have ht := a.finiteLearner_transfer mu P hcap
  refine ⟨?_,?_⟩
  · rw [add_div,← sub_sub]
    exact (sub_le_sub_right hr.1 _).trans ht.1
  · intro i
    rw [add_div,← sub_sub]
    exact (sub_le_sub_right (hr.2 i) _).trans (ht.2 i)

lemma FairCalibrationParameters.finiteLearner_accepts_cap
    (a : FairCalibrationParameters n m) (mu : ℝ)
    (y : Reservoir n (2*m)) (r : (a.finiteLearner mu).Seed)
    (t : ℝ) (i : Fin n) (H : History n) :
    (a.finiteLearner mu).rankToClock.policy.decide (y,r) t i 1 H=true := by
  letI : NeZero m := ⟨by have := a.two_le; omega⟩
  rw [RankLearner.rankToClock_policy]
  change (a.finiteLearner mu).policy.decide (y,r) (currentRankFromClock i H) i 1 (rankHistoryFromClock i H)=true
  exact finiteRankCalibratedLearner_accepts_cap (J := a.grid) a.clockBits a.coinBits
    a.targetLaw a.thresholdLaw mu a.zlo (1/4) a.target a.threshold a.measurable_target a.measurable_threshold
    y r _ i _

/-- The actual fair-bit rank execution has a hard sample budget of order
(1/\varepsilon), for arbitrary original independent nonnegative laws with
positive finite expected maximum. -/
theorem finite_bit_outer_sample_upper_bound :
    ∃ (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (zInv : ℕ)
      (hInv : 1/((1-(b : ℝ))/(b : ℝ))≤(zInv : ℝ)) (A eps0 : ℝ),
      0<A ∧ 0<eps0 ∧ ∀ eps∈Ioo (0 : ℝ) eps0,
        ∃ (m : ℕ) (hm : 2≤m), (outerSampleBudget m : ℝ)≤A/eps ∧
          ∀ (n : ℕ) (hn : 0<n),
            let a : FairCalibrationParameters n m :=
              ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
            (outerFairRankLearner (by omega : 1≤m) (a.finiteLearner (1/10000000))
              (outerMarkBits n m)).Guarantees (optimalCompetitiveRatio-eps) := by
  have hμ : (0 : ℝ)<1/10000000 := by norm_num
  have hμ' : (1/10000000 : ℝ)<1/80 := by norm_num
  obtain ⟨b,hb,zInv,hInv,K,hK,hStat⟩ := exists_finite_rank_calibrated_learner _ hμ hμ'
  let params (n m : ℕ) (hn : 0<n) (hm : 2≤m) : FairCalibrationParameters n m :=
    ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
  let L (n m : ℕ) (hn : 0<n) (hm : 2≤m) := (params n m hn hm).finiteLearner (1/10000000)
  refine ⟨b,hb,zInv,hInv,?_⟩
  apply fair_rank_outer_at_accuracy_of_bounded hK.le L
  intro n m hn hm P hMean hL _ hcap
  dsimp only
  have hB := hStat n m hn hm P hcap hMean.1 hMean.2 hL
  refine ⟨Filter.Eventually.of_forall (fun ω i _ hx => ?_), ?_, ?_⟩
  · change (L n m hn hm).rankToClock.policy.decide ω.2.2 (ω.2.1 i) i (ω.1 i) _=true
    rw [hx]
    exact (params n m hn hm).finiteLearner_accepts_cap (1/10000000)
      ω.2.2.1 ω.2.2.2 _ i _
  · rw [RankLearner.rankToClock_expectedReward]
    exact hB.1
  · intro i
    rw [RankLearner.rankToClock_reachProbability]
    exact hB.2 i

/-- A fixed rational mean floor can be used in the entire finite-bit
construction while retaining every instance in the original class. -/
theorem exists_rational_finite_rank_calibrated_learner (mu : ℝ) (hmu : 0<mu) (hmuHi : mu<1/80) :
    ∃ mu' : ℚ, mu/2≤(mu' : ℝ) ∧ (mu' : ℝ)≤mu ∧
      ∃ (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (zInv : ℕ)
        (hInv : 1/((1-(b : ℝ))/(b : ℝ))≤(zInv : ℝ)) (K : ℝ), 0<K ∧
        ∀ (n m : ℕ) (hn : 0<n) (hm : 2≤m) (P : Instance n),
          (∀ i, ∀ᵐ x ∂P.law i, x≤1) → mu≤P.expectedMaximum → P.expectedMaximum≤1/80 →
          P.positiveCount≤2*Real.log (m : ℝ) →
          let a : FairCalibrationParameters n m :=
            ⟨(1-(b : ℝ))/(b : ℝ),zInv,hn,hm,calibrationEndpoint_coefficient_bounds hb,hInv⟩
          let L := a.finiteLearner (mu' : ℝ)
          optimalCompetitiveRatio*P.expectedMaximum-K/(m : ℝ)≤L.expectedReward P ∧
          ∀ i, optimalCompetitiveRatio-K/(m : ℝ)≤L.reachProbability P i := by
  obtain ⟨r,hr,hr'⟩ := exists_rat_btwn (show mu/2<mu by linarith only [hmu])
  have hr0 : 0<(r : ℝ) := (by linarith only [hmu] : 0<mu/2).trans hr
  obtain ⟨b,hb,zInv,hInv,K,hK,hBound⟩ :=
    exists_finite_rank_calibrated_learner (r : ℝ) hr0 (hr'.trans hmuHi)
  refine ⟨r,hr.le,hr'.le,b,hb,zInv,hInv,K,hK,?_⟩
  intro n m hn hm P hcap hMean hSmall hL
  exact hBound n m hn hm P hcap (hr'.le.trans hMean) hSmall hL

end ProphetSecretary.Statistics.Calibration
