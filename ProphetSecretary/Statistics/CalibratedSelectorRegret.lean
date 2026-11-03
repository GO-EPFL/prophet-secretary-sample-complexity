import ProphetSecretary.Statistics.CalibratedSelectorExecution
import ProphetSecretary.Statistics.CalibratedSelectedRegretBound

/-!
# Regret of a measurable offline selector

The comparison bound allows any selector of an empirical block and grid
segment with the prescribed information. In particular it applies to the
interpolation based on reported timestamps.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m]

section

variable (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (zlo : ℝ) (policyEstimate : ContinuationEstimator n m PSeed)
    (A : OfflineData n m J TSeed PSeed → PreparedCalibration n m) (hA : Measurable A)
    (hBounds : ∀ d, 1≤(A d).2.1 ∧ (A d).2.1≤J+2 ∧ (A d).2.2∈Ioc (0 : ℝ) 1)
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))

local notation "D" => OfflineData n m J TSeed PSeed
local notation "O" => offlineDataLaw (m := m) (J := J) P νT νP
local notation "C" => selectorConditionalPolicy νP zlo (1/4) policyEstimate A hC

noncomputable def selectorCoefficient (d : D) : ℝ :=
  selectedCoefficient zlo (1/4) J (A d).2

local notation "Z" => selectorCoefficient zlo A

omit [NeZero m] in
include hA in
lemma measurable_selectorCoefficient : Measurable Z := by
  classical
  let k := fun d : D => (A d).2.1
  let α := fun d : D => (A d).2.2
  have hk : Measurable k := measurable_fst.comp (measurable_snd.comp hA)
  have hα : Measurable α := measurable_snd.comp (measurable_snd.comp hA)
  have hLow := (measurable_of_countable
    (fun j : ℕ => familyCoefficient zlo (1/4) J (lowerPolicyIndex J j).val)).comp hk
  have hHi := (measurable_of_countable
    (fun j : ℕ => familyCoefficient zlo (1/4) J (upperPolicyIndex J j).val)).comp hk
  have hK : MeasurableSet {d : D | k d=1} := measurableSet_eq_fun hk measurable_const
  have hB := (((measurable_const (a := (1 : ℝ))).sub hα).mul hLow).add (hα.mul hHi)
  change Measurable (fun d : D => if k d=1 then (0 : ℝ) else
    (1-α d)*familyCoefficient zlo (1/4) J (lowerPolicyIndex J (k d)).val+
      α d*familyCoefficient zlo (1/4) J (upperPolicyIndex J (k d)).val)
  apply Measurable.ite hK measurable_const
  convert hB using 1
  funext d
  rfl

omit [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m] in
include hBounds in
lemma selectorCoefficient_range (h0 : 0≤zlo) (hz : zlo≤1/4) (d : D) :
    Z d∈Icc (0 : ℝ) (1/4) :=
  selectedCoefficient_range h0 hz J _ ⟨(hBounds d).2.2.1.le,
    (hBounds d).2.2.2⟩

omit [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m] in
lemma selectorCoefficient_left (d : D) (hl : (A d).2.1=1) : Z d=0 := by
  simp only [selectorCoefficient,selectedCoefficient,hl,if_true]

noncomputable def selectorRegret (b : ℝ) (d : D) : ℝ :=
  if (A d).2.1=1 then (C d).normalizedRegret P b
  else optimalScalarValue P 1 (Z d)-(C d).scalarObjective P 1 (Z d)

local notation "r" => selectorRegret P νP zlo policyEstimate A hC

omit [MeasurableSpace TSeed] in
include hBounds in
lemma selectorRegret_nonnegative (hP : Integrable Instance.maximum P.valuesLaw)
    (h0 : 0≤zlo) (hz : zlo≤1/4) {b : ℝ} (hb : b∈Icc (0 : ℝ) 1) (d : D) :
    0≤r b d := by
  unfold selectorRegret
  split_ifs
  · exact (C d).normalizedRegret_nonnegative P hP hb
  · exact sub_nonneg.mpr (scalarObjective_le_optimal (C d) P hP zero_le_one
      (selectorCoefficient_range zlo A hBounds h0 hz d).1)

include hA hBounds in
lemma integrable_selectorRegret (hP : Integrable Instance.maximum P.valuesLaw)
    (h0 : 0≤zlo) (hz : zlo≤1/4) {b : ℝ} (hb : b∈Icc (0 : ℝ) 1) :
    Integrable (r b) O := by
  have hRI := integrable_selectorConditionalReward P νT νP zlo (1/4) policyEstimate A hA hC hP
  have hTI := integrable_selectorConditionalDuration P νT νP zlo (1/4) policyEstimate A hA hC
  have hZ := measurable_selectorCoefficient zlo A hA
  have hZrange := selectorCoefficient_range zlo A hBounds h0 hz
  have hV := P.measurable_scalarValue_coefficients hP (measurable_const (a := (1 : ℝ))) hZ
    (fun _ => zero_le_one) (fun d => (hZrange d).1)
  have hVb : AEMeasurable (fun _ : D => optimalScalarValue P b (1-b)) O := aemeasurable_const
  have hLeft := hVb.sub
    ((hRI.aemeasurable.const_mul b).add (hTI.aemeasurable.const_mul (1-b)))
  have hMid := hV.aemeasurable.sub (hRI.aemeasurable.add (hZ.aemeasurable.mul hTI.aemeasurable))
  have hK : MeasurableSet {d : D | (A d).2.1=1} :=
    measurableSet_eq_fun (measurable_fst.comp (measurable_snd.comp hA)) measurable_const
  have hR : AEMeasurable (r b) O := by
    change AEMeasurable (fun d : D => r b d) O
    simp only [selectorRegret,RandomizedPolicy.normalizedRegret,
      RandomizedPolicy.scalarObjective_eq _ P hP,one_mul]
    let L := hLeft.mk _
    let U := hMid.mk _
    have hm : Measurable (fun d : D => if (A d).2.1=1 then L d else U d) :=
      Measurable.ite hK hLeft.measurable_mk hMid.measurable_mk
    apply hm.aemeasurable.congr
    filter_upwards [hLeft.ae_eq_mk,hMid.ae_eq_mk] with d hL hU
    by_cases hd : (A d).2.1=1
    · simpa only [if_pos hd,L,Pi.sub_apply,Pi.add_apply] using hL.symm
    · simpa only [if_neg hd,U,Pi.sub_apply,Pi.add_apply,Pi.mul_apply] using hU.symm
  apply Integrable.of_bound hR.aestronglyMeasurable (P.expectedMaximum+1)
  exact Filter.Eventually.of_forall fun d => by
    rw [Real.norm_eq_abs,abs_of_nonneg
      (selectorRegret_nonnegative P νP zlo policyEstimate A hBounds hC hP h0 hz hb d)]
    unfold selectorRegret
    split_ifs
    · unfold RandomizedPolicy.normalizedRegret
      have hVb := optimalScalarValue_le_benchmark P hP hb.1 (sub_nonneg.mpr hb.2)
      have hJ := (C d).scalarObjective_nonnegative P hP hb.1 (sub_nonneg.mpr hb.2)
      linarith only [hVb,hJ,mul_le_of_le_one_left P.expectedMaximum_nonnegative hb.2,hb.1]
    · have hVb := optimalScalarValue_le_benchmark P hP zero_le_one (hZrange d).1
      have hJ := (C d).scalarObjective_nonnegative P hP zero_le_one (hZrange d).1
      linarith only [hVb,hJ,(hZrange d).2]

end

theorem selectorRegret_le_of_coupling (P : Instance n)
    (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hM : P.expectedMaximum≤1/80)
    (hL : P.positiveCount≤2*Real.log (m : ℝ)) {b : ℝ} (hb : b∈Ioo (4/5 : ℝ) 1)
    (hJ : 0<J) (hSize : (m : ℝ)*(1/4-(1-b)/b)≤(J : ℝ))
    (policyEstimate : ContinuationEstimator n m PSeed)
    (A : OfflineData n m J TSeed PSeed → PreparedCalibration n m) (hA : Measurable A)
    (hQ : ∀ d, (A d).1=offlineEmpiricalBlock d)
    (hBounds : ∀ d, 1≤(A d).2.1 ∧ (A d).2.1≤J+2 ∧ (A d).2.2∈Ioc (0 : ℝ) 1)
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (hCouple : ∀ᵐ d ∂offlineDataLaw (m := m) (J := J) P νT νP,
      empiricalPositiveCount d.1.1≤targetCountCutoff m → ∀ j : Fin (J+1),
        let zlo := (1-b)/b
        let z := familyCoefficient zlo (1/4) J j.val
        let q := offlineEmpiricalBlock d
        (exactCalibrationEndpoint q z).scalarObjective P 1 z-
          (numericalCalibrationEndpoint νP zlo (1/4) policyEstimate hC q j).scalarObjective P 1 z≤4/(m : ℝ)) :
    (∫ d, selectorRegret P νP ((1-b)/b) policyEstimate A hC b d
      ∂offlineDataLaw P νT νP)≤
        (2*empiricalCapRegretConstant ((1-b)/b)+7)*(1+P.totalFirstMoment*(1+P.totalFirstMoment))/(m : ℝ) := by
  let D := OfflineData n m J TSeed PSeed
  let O := offlineDataLaw (m := m) (J := J) P νT νP
  let zlo := (1-b)/b
  let C := selectorConditionalPolicy νP zlo (1/4) policyEstimate A hC
  let Z := selectorCoefficient zlo A
  let r := selectorRegret P νP zlo policyEstimate A hC b
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
  have hk := measurable_fst.comp (measurable_snd.comp hA)
  have hzL : Measurable (fun d => z (jL d)) := (measurable_of_countable (z ∘ lowerPolicyIndex J)).comp hk
  have hzU : Measurable (fun d => z (jU d)) := (measurable_of_countable (z ∘ upperPolicyIndex J)).comp hk
  have hZR (j : Fin (J+1)) : z j∈Icc zlo (1/4) := familyCoefficient_range hz.2.le J j.val
  have hEL := exactCalibrationEndpoint_selected_regret_le P νT νP hcap hM hz.1 hz.2.le _ hzL (fun d => hZR (jL d))
  have hEU := exactCalibrationEndpoint_selected_regret_le P νT νP hcap hM hz.1 hz.2.le _ hzU (fun d => hZR (jU d))
  have hr := integrable_selectorRegret P νT νP zlo policyEstimate A hA hBounds hC
    hP hz.1.le hz.2.le hbI
  have hES : MeasurableSet {v : D | targetCountCutoff m<empiricalPositiveCount v.1.1} :=
    measurableSet_lt measurable_const (measurable_empiricalPositiveCount.comp (measurable_fst.comp measurable_fst))
  have he : Integrable e O := (integrable_const (1 : ℝ)).indicator hES
  have hR (d : D) : Z d∈Icc (0 : ℝ) (1/4) :=
    selectorCoefficient_range zlo A hBounds hz.1.le hz.2.le d
  have hE0 (d : D) (j : Fin (J+1)) : 0≤E d j :=
    exactCalibrationEndpoint_regret_nonnegative P hP (q d) (hz.1.le.trans (hZR j).1)
  have hPoint : ∀ᵐ d ∂O, r d≤E d (jL d)+E d (jU d)+6/(m : ℝ)+e d := by
    filter_upwards [hCouple] with d hd
    let p := A d
    let k := p.2.1
    let α := p.2.2
    let π := C d
    let N := fun j : Fin (J+1) => numericalCalibrationEndpoint νP zlo (1/4) policyEstimate hC (q d) j
    obtain ⟨hk0,hk1,hα⟩ := hBounds d
    change 1≤k at hk0
    change k≤J+2 at hk1
    have hα0 : 0≤α := hα.1.le
    have hα1 : 0≤1-α := sub_nonneg.mpr hα.2
    let hαI : α∈Icc (0 : ℝ) 1 := ⟨hα.1.le,hα.2⟩
    have hMix (w u : ℝ) : π.scalarObjective P w u=(1-α)*(N (jL d)).scalarObjective P w u+
        α*(N (jU d)).scalarObjective P w u  := by
      have h := preparedPolicy_scalarObjective_eq (J := J) P hP νP zlo (1/4) policyEstimate hC p hαI w u
      have hq : p.1=q d := hQ d
      dsimp only at h
      rw [hq] at h
      exact h
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
