import ProphetSecretary.Statistics.CalibratedSelectedPoint
import ProphetSecretary.Statistics.CalibrationExactRegret
import ProphetSecretary.Statistics.CalibrationAdaptation

/-!
# Selected-policy regret after continuation approximation

The exact empirical endpoints may depend on both blocks. On the regular
event, coupling transfers scalar payoff to the numerical endpoint. A
mesh interval changes regret by at most twice its width. The remaining
empirical count fallback is charged its probability.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m]

noncomputable def numericalCalibrationEndpoint (νP : Measure PSeed) [IsProbabilityMeasure νP]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (q : Reservoir n m) (j : Fin (J+1)) : RandomizedPolicy n :=
  RandomizedPolicy.ofRule (policyQueryArrayLaw νP) (frozenFamilyPolicy zlo zhi estimate q j)
    (frozenFamilyPolicy_isMeasurable zlo zhi estimate he q j)

lemma preparedPolicy_scalarObjective_eq (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (νP : Measure PSeed) [IsProbabilityMeasure νP] (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (p : PreparedCalibration n m) (hα : p.2.2∈Icc (0 : ℝ) 1) (w z : ℝ) :
    let π := RandomizedPolicy.ofRule (onlineCalibrationSeedLaw (J := J) νP)
      (preparedPolicy zlo zhi estimate p) (preparedPolicy_isMeasurable zlo zhi estimate he p)
    let L := numericalCalibrationEndpoint νP zlo zhi estimate he p.1 (lowerPolicyIndex J p.2.1)
    let U := numericalCalibrationEndpoint νP zlo zhi estimate he p.1 (upperPolicyIndex J p.2.1)
    π.scalarObjective P w z=(1-p.2.2)*L.scalarObjective P w z+p.2.2*U.scalarObjective P w z := by
  let L := numericalCalibrationEndpoint νP zlo zhi estimate he p.1 (lowerPolicyIndex J p.2.1)
  let U := numericalCalibrationEndpoint νP zlo zhi estimate he p.1 (upperPolicyIndex J p.2.1)
  let π := RandomizedPolicy.ofRule (onlineCalibrationSeedLaw (J := J) νP)
    (preparedPolicy zlo zhi estimate p) (preparedPolicy_isMeasurable zlo zhi estimate he p)
  change π.scalarObjective P w z=(1-p.2.2)*L.scalarObjective P w z+p.2.2*U.scalarObjective P w z
  have hR : π.expectedReward P=(1-p.2.2)*L.expectedReward P+p.2.2*U.expectedReward P :=
    L.rule.uniformMix_expectedReward U.rule L.measurable_rule U.measurable_rule P hP L.seedLaw hα
  have hT : π.expectedDuration P=(1-p.2.2)*L.expectedDuration P+p.2.2*U.expectedDuration P :=
    L.rule.uniformMix_meanDuration U.rule L.measurable_rule U.measurable_rule P L.seedLaw hα
  rw [π.scalarObjective_eq P hP,L.scalarObjective_eq P hP,U.scalarObjective_eq P hP,hR,hT]
  ring

lemma preparedPolicy_reach_eq_mean (P : Instance n)
    (νP : Measure PSeed) [IsProbabilityMeasure νP] (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (p : PreparedCalibration n m) (hα : p.2.2∈Icc (0 : ℝ) 1) (i : Fin n) :
    let L := numericalCalibrationEndpoint νP zlo zhi estimate he p.1 (lowerPolicyIndex J p.2.1)
    let U := numericalCalibrationEndpoint νP zlo zhi estimate he p.1 (upperPolicyIndex J p.2.1)
    (preparedPolicy zlo zhi estimate p).reachProbability P (onlineCalibrationSeedLaw (J := J) νP) i =
      (1-p.2.2)*L.rule.reachProbability P L.seedLaw i+p.2.2*U.rule.reachProbability P U.seedLaw i := by
  let L := numericalCalibrationEndpoint νP zlo zhi estimate he p.1 (lowerPolicyIndex J p.2.1)
  let U := numericalCalibrationEndpoint νP zlo zhi estimate he p.1 (upperPolicyIndex J p.2.1)
  exact L.rule.uniformMix_reachProbability U.rule L.measurable_rule U.measurable_rule P L.seedLaw hα i

lemma preparedPolicy_duration_eq_mean (P : Instance n)
    (νP : Measure PSeed) [IsProbabilityMeasure νP] (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (p : PreparedCalibration n m) (hα : p.2.2∈Icc (0 : ℝ) 1) :
    let L := numericalCalibrationEndpoint νP zlo zhi estimate he p.1 (lowerPolicyIndex J p.2.1)
    let U := numericalCalibrationEndpoint νP zlo zhi estimate he p.1 (upperPolicyIndex J p.2.1)
    (preparedPolicy zlo zhi estimate p).meanDuration P (onlineCalibrationSeedLaw (J := J) νP) =
      (1-p.2.2)*L.expectedDuration P+p.2.2*U.expectedDuration P := by
  let L := numericalCalibrationEndpoint νP zlo zhi estimate he p.1 (lowerPolicyIndex J p.2.1)
  let U := numericalCalibrationEndpoint νP zlo zhi estimate he p.1 (upperPolicyIndex J p.2.1)
  exact L.rule.uniformMix_meanDuration U.rule L.measurable_rule U.measurable_rule P L.seedLaw hα

lemma offline_count_cutoff_probability_le (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (hL : P.positiveCount≤2*Real.log (m : ℝ)) :
    (offlineDataLaw (m := m) (J := J) P νT νP).real
      {d | targetCountCutoff m<empiricalPositiveCount d.1.1}≤1/(m : ℝ) := by
  let D := OfflineData n m J TSeed PSeed
  let E := {a : (Fin n × Fin m) → ℝ | targetCountCutoff m<empiricalPositiveCount a}
  have hE : MeasurableSet E := measurableSet_lt measurable_const measurable_empiricalPositiveCount
  have hp : MeasurePreserving (fun d : D => d.1.1) (offlineDataLaw P νT νP) (P.trainingCoordinateLaw m) :=
    measurePreserving_fst.comp measurePreserving_fst
  have hP := empiricalPositiveCount_cutoff_probability P hL
  have hEq : (offlineDataLaw (m := m) (J := J) P νT νP).real
      {d | targetCountCutoff m<empiricalPositiveCount d.1.1}=(P.trainingCoordinateLaw m).real E := by
    have h := map_measureReal_apply (μ := offlineDataLaw (m := m) (J := J) P νT νP) hp.measurable hE
    rw [hp.map_eq] at h
    exact h.symm
  rw [hEq]
  refine hP.trans ?_
  have hm : (0 : ℝ)<m := Nat.cast_pos.mpr (NeZero.pos m)
  rw [show -2*(m : ℝ)=-(2*(m : ℝ)) by ring,Real.exp_neg,one_div]
  exact (inv_le_inv₀ (Real.exp_pos _) hm).mpr (by linarith [Real.add_one_le_exp (2*(m : ℝ))])

theorem offline_selectedRegret_le_of_coupling (P : Instance n)
    (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hM : P.expectedMaximum≤1/80)
    (hL : P.positiveCount≤2*Real.log (m : ℝ)) {b : ℝ} (hb : b∈Ioo (4/5 : ℝ) 1)
    (hJ : 0<J) (hSize : (m : ℝ)*(1/4-(1-b)/b)≤(J : ℝ)) (mu : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (hCouple : ∀ᵐ d ∂offlineDataLaw (m := m) (J := J) P νT νP,
      empiricalPositiveCount d.1.1≤targetCountCutoff m → ∀ j : Fin (J+1),
        let zlo := (1-b)/b
        let z := familyCoefficient zlo (1/4) J j.val
        let q := offlineEmpiricalBlock d
        (exactCalibrationEndpoint q z).scalarObjective P 1 z-
          (numericalCalibrationEndpoint νP zlo (1/4) policyEstimate hC q j).scalarObjective P 1 z≤4/(m : ℝ)) :
    (∫ d, offlineSelectedRegret (J := J) P νP mu ((1-b)/b) targetEstimate policyEstimate hC b d
      ∂offlineDataLaw P νT νP)≤
        (2*empiricalCapRegretConstant ((1-b)/b)+7)*(1+P.totalFirstMoment*(1+P.totalFirstMoment))/(m : ℝ) := by
  let D := OfflineData n m J TSeed PSeed
  let O := offlineDataLaw (m := m) (J := J) P νT νP
  let zlo := (1-b)/b
  let A := offlinePrepare (J := J) mu zlo (1/4) targetEstimate policyEstimate
  let C := conditionalCalibrationPolicy (J := J) νP mu zlo (1/4) targetEstimate policyEstimate hC
  let Z := offlineSelectedCoefficient (J := J) mu zlo targetEstimate policyEstimate
  let r := offlineSelectedRegret (J := J) P νP mu zlo targetEstimate policyEstimate hC b
  let jL := fun d : D => lowerPolicyIndex J (A d).2.1
  let jU := fun d : D => upperPolicyIndex J (A d).2.1
  let z := fun j : Fin (J+1) => familyCoefficient zlo (1/4) J j.val
  let q := offlineEmpiricalBlock (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed)
  let e := fun d : D => {v : D | targetCountCutoff m<empiricalPositiveCount v.1.1}.indicator (1 : D → ℝ) d
  let E := fun (d : D) (j : Fin (J+1)) => optimalScalarValue P 1 (z j)-
    (exactCalibrationEndpoint (q d) (z j)).scalarObjective P 1 (z j)
  have hz := calibrationEndpoint_coefficient_bounds hb
  have hbI : b∈Icc (0 : ℝ) 1 := ⟨(by norm_num : (0 : ℝ)≤4/5).trans hb.1.le,hb.2.le⟩
  have hbP : b∈Ioc (0 : ℝ) 1 := ⟨(by norm_num : (0 : ℝ)<4/5).trans hb.1,hb.2.le⟩
  have hP := P.integrable_maximum_of_bounded hcap
  have hm : (0 : ℝ)<m := Nat.cast_pos.mpr (NeZero.pos m)
  have hA := measurable_offlinePrepare (J := J) mu zlo (1/4) targetEstimate policyEstimate hT hC
  have hk := measurable_fst.comp (measurable_snd.comp hA)
  have hzL : Measurable (fun d => z (jL d)) := (measurable_of_countable (z ∘ lowerPolicyIndex J)).comp hk
  have hzU : Measurable (fun d => z (jU d)) := (measurable_of_countable (z ∘ upperPolicyIndex J)).comp hk
  have hZR (j : Fin (J+1)) : z j∈Icc zlo (1/4) := familyCoefficient_range hz.2.le J j.val
  have hEL := exactCalibrationEndpoint_selected_regret_le P νT νP hcap hM hz.1 hz.2.le _ hzL (fun d => hZR (jL d))
  have hEU := exactCalibrationEndpoint_selected_regret_le P νT νP hcap hM hz.1 hz.2.le _ hzU (fun d => hZR (jU d))
  have hr := integrable_offlineSelectedRegret (J := J) P νT νP mu zlo targetEstimate policyEstimate hT hC
    hP hz.1.le hz.2.le hbI
  have hES : MeasurableSet {v : D | targetCountCutoff m<empiricalPositiveCount v.1.1} :=
    measurableSet_lt measurable_const (measurable_empiricalPositiveCount.comp (measurable_fst.comp measurable_fst))
  have he : Integrable e O := (integrable_const (1 : ℝ)).indicator hES
  have hR (d : D) : Z d∈Icc (0 : ℝ) (1/4) :=
    offlineSelectedCoefficient_range mu zlo targetEstimate policyEstimate hz.1.le hz.2.le d
  have hE0 (d : D) (j : Fin (J+1)) : 0≤E d j :=
    exactCalibrationEndpoint_regret_nonnegative P hP (q d) (hz.1.le.trans (hZR j).1)
  have hPoint : ∀ᵐ d ∂O, r d≤E d (jL d)+E d (jU d)+6/(m : ℝ)+e d := by
    filter_upwards [hCouple] with d hd
    let p := A d
    let k := p.2.1
    let α := p.2.2
    let π := C d
    let N := fun j : Fin (J+1) => numericalCalibrationEndpoint νP zlo (1/4) policyEstimate hC (q d) j
    obtain ⟨hk0,hk1,hα⟩ := offlinePrepare_bounds mu zlo (1/4) targetEstimate policyEstimate d
    change 1≤k at hk0
    change k≤J+2 at hk1
    have hα0 : 0≤α := hα.1.le
    have hα1 : 0≤1-α := sub_nonneg.mpr hα.2
    let hαI : α∈Icc (0 : ℝ) 1 := ⟨hα.1.le,hα.2⟩
    have hMix (w u : ℝ) : π.scalarObjective P w u=(1-α)*(N (jL d)).scalarObjective P w u+
        α*(N (jU d)).scalarObjective P w u := preparedPolicy_scalarObjective_eq P hP νP zlo (1/4)
      policyEstimate hC p hαI w u
    have hEndpoint (j : Fin (J+1)) {u : ℝ} (hu : u∈Icc (0 : ℝ) (1/4))
        (hDist : |u-z j|≤1/(m : ℝ)) :
        optimalScalarValue P 1 u-(N j).scalarObjective P 1 u≤E d j+6/(m : ℝ)+e d := by
      by_cases hReg : empiricalPositiveCount d.1.1≤targetCountCutoff m
      · have hC' := hd hReg j
        have hD := calibration_unnormalized_regret_coefficient_change P (N j) hP hu.1
          (hz.1.le.trans (hZR j).1)
        have hmem : d∉{v : D | targetCountCutoff m<empiricalPositiveCount v.1.1} := not_lt_of_ge hReg
        have he0 : e d=0 := Set.indicator_of_notMem hmem _
        change (exactCalibrationEndpoint (q d) (z j)).scalarObjective P 1 (z j)-
          (N j).scalarObjective P 1 (z j)≤4/(m : ℝ) at hC'
        change optimalScalarValue P 1 u-(N j).scalarObjective P 1 u≤
          optimalScalarValue P 1 (z j)-(N j).scalarObjective P 1 (z j)+2*|u-z j| at hD
        rw [he0]
        calc
          _ ≤ _ := hD
          _ = E d j+((exactCalibrationEndpoint (q d) (z j)).scalarObjective P 1 (z j)-
              (N j).scalarObjective P 1 (z j))+2*|u-z j| := by dsimp [E]; ring
          _ ≤ E d j+4/(m : ℝ)+2*(1/(m : ℝ)) :=
            add_le_add (add_le_add le_rfl hC') (mul_le_mul_of_nonneg_left hDist (by norm_num))
          _ = _ := by ring
      · have hV := optimalScalarValue_le_benchmark P hP zero_le_one hu.1
        have hJ := (N j).scalarObjective_nonnegative P hP zero_le_one hu.1
        have hmem : d∈{v : D | targetCountCutoff m<empiricalPositiveCount v.1.1} := lt_of_not_ge hReg
        have he1 : e d=1 := Set.indicator_of_mem hmem _
        rw [he1]
        linarith only [hV,hJ,hu.2,hM,hE0 d j,div_nonneg (by norm_num : (0 : ℝ)≤6) hm.le]
    have hSum {u : ℝ} (hu : u∈Icc (0 : ℝ) (1/4))
        (ha : |u-z (jL d)|≤1/(m : ℝ)) (hb' : |u-z (jU d)|≤1/(m : ℝ)) :
        optimalScalarValue P 1 u-π.scalarObjective P 1 u≤E d (jL d)+E d (jU d)+6/(m : ℝ)+e d := by
      have h1 := mul_le_mul_of_nonneg_left (hEndpoint (jL d) hu ha) hα1
      have h2 := mul_le_mul_of_nonneg_left (hEndpoint (jU d) hu hb') hα0
      have hL := mul_le_of_le_one_left (hE0 d (jL d)) (show 1-α≤1 by linarith)
      have hU := mul_le_of_le_one_left (hE0 d (jU d)) (show α≤1 from hα.2)
      rw [hMix]
      nlinarith only [h1,h2,hL,hU]
    by_cases hl : k=1
    · have h0 : z (jL d)=zlo := by
        change familyCoefficient zlo (1/4) J (lowerPolicyIndex J k).val=_
        rw [hl,lowerPolicyIndex_first]; exact familyCoefficient_zero _ _ _
      have h1 : z (jU d)=zlo := by
        change familyCoefficient zlo (1/4) J (upperPolicyIndex J k).val=_
        rw [hl,upperPolicyIndex_first]; exact familyCoefficient_zero _ _ _
      have h := hSum (show zlo∈Icc (0 : ℝ) (1/4) from ⟨hz.1.le,hz.2.le⟩)
        (by rw [h0,sub_self,abs_zero]; positivity) (by rw [h1,sub_self,abs_zero]; positivity)
      have hN := normalized_value_difference_eq_scaled π P hP hbP
      change (if k=1 then π.normalizedRegret P b else
        optimalScalarValue P 1 (Z d)-π.scalarObjective P 1 (Z d))≤_
      rw [if_pos hl]
      unfold RandomizedPolicy.normalizedRegret
      rw [hN]
      change b*(optimalScalarValue P 1 zlo-π.scalarObjective P 1 zlo)≤_
      exact (mul_le_of_le_one_left (sub_nonneg.mpr (scalarObjective_le_optimal π P hP zero_le_one hz.1.le))
        hb.2.le).trans h
    · have hDist := selectedCoefficient_distance_endpoints (NeZero.pos m) hJ hz.2.le hSize
        (show 2≤k from by omega) hk1 hαI
      have h := hSum (hR d) hDist.1 hDist.2
      change (if k=1 then π.normalizedRegret P b else
        optimalScalarValue P 1 (Z d)-π.scalarObjective P 1 (Z d))≤_
      rw [if_neg hl]
      exact h
  have hRInt := integral_mono_ae hr (((hEL.1.add hEU.1).add (integrable_const (6/(m : ℝ)))).add he) hPoint
  change (∫ d,r d ∂O)≤∫ d,E d (jL d)+E d (jU d)+6/(m : ℝ)+e d ∂O at hRInt
  rw [integral_add (f := fun d => E d (jL d)+E d (jU d)+6/(m : ℝ)) (g := e)
      ((hEL.1.add hEU.1).add (integrable_const (6/(m : ℝ)))) he,
    integral_add (f := fun d => E d (jL d)+E d (jU d)) (g := fun _ => 6/(m : ℝ))
      (hEL.1.add hEU.1) (integrable_const (6/(m : ℝ))),
    integral_add hEL.1 hEU.1,integral_const,probReal_univ,one_smul] at hRInt
  have heq : (∫ d,e d ∂O)=(O).real {d | targetCountCutoff m<empiricalPositiveCount d.1.1} :=
    integral_indicator_one hES
  rw [heq] at hRInt
  have hCut := offline_count_cutoff_probability_le (J := J) P νT νP hL
  have hS0 : 0≤P.totalFirstMoment := Finset.sum_nonneg (fun i _ => integral_nonneg_of_ae (P.nonnegative i))
  have hK : 1≤1+P.totalFirstMoment*(1+P.totalFirstMoment) := by nlinarith
  have hErr := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by norm_num : (0 : ℝ)≤7)) hm.le
  change (∫ d,r d ∂O)≤(2*empiricalCapRegretConstant zlo+7)*(1+P.totalFirstMoment*(1+P.totalFirstMoment))/(m : ℝ)
  let F := 1+P.totalFirstMoment*(1+P.totalFirstMoment)
  let B := empiricalCapRegretConstant zlo
  have hIntL : (∫ d,E d (jL d) ∂O)≤B*F/(m : ℝ) := hEL.2
  have hIntU : (∫ d,E d (jU d) ∂O)≤B*F/(m : ℝ) := hEU.2
  change (∫ d,r d ∂O)≤(∫ d,E d (jL d) ∂O)+(∫ d,E d (jU d) ∂O)+
    6/(m : ℝ)+(O).real {d | targetCountCutoff m<empiricalPositiveCount d.1.1} at hRInt
  calc
    _ ≤ _ := hRInt
    _ ≤ B*F/(m : ℝ)+B*F/(m : ℝ)+6/(m : ℝ)+1/(m : ℝ) :=
      add_le_add (add_le_add (add_le_add hIntL hIntU) le_rfl) hCut
    _ = 2*B*F/(m : ℝ)+7*1/(m : ℝ) := by ring
    _ ≤ 2*B*F/(m : ℝ)+7*F/(m : ℝ) := add_le_add le_rfl hErr
    _ = _ := by change _=(2*B+7)*F/(m : ℝ); ring

end ProphetSecretary.Statistics.Calibration
