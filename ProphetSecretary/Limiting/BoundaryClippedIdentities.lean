import ProphetSecretary.Limiting.CountableRewardClipping
import ProphetSecretary.Limiting.CountableCapBenchmark
import ProphetSecretary.Limiting.CountableCapExcessPrefix
import ProphetSecretary.Limiting.NoReserve
import ProphetSecretary.Model.HalfGuarantee

/-!
# Equality consequences at a normalized reward-critical instance

Actual clipping, the global scalar inequality, and the prophet excess bound
force equality throughout C≤C(M_cap+e)≤V_new≤C. The cap benchmark is at most C,
so the duration coefficient e is positive. Aggregate excess then equals the
expected maximum excess, the hypothesis used for excess concentration.
-/

open MeasureTheory Set
open scoped NNReal Classical
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

theorem boundary_clipped_identities (B : CountableInstance) (hZero : B.terminal=0)
    (hM : B.expectedMaximum=1) (hV : B.optimalScalarValue 1 0=optimalCompetitiveRatio)
    (K : ℝ≥0) (hK : 0<K) (hKC : (K:ℝ)=optimalCompetitiveRatio) :
    let Q := B.capAt hZero K hK
    let e := B.totalCapExcess K
    e∈Icc (1-optimalCompetitiveRatio) optimalCompetitiveRatio ∧
    0<e ∧ Q.optimalScalarValue 1 e=optimalCompetitiveRatio ∧ Q.expectedMaximum+e=1 ∧
      e=∫ v, Model.tailValue K (B.maximum v) ∂B.valueLaw := by
  have hC : 0<optimalCompetitiveRatio := (by norm_num : (0:ℝ)<1/2).trans_le half_le_optimalCompetitiveRatio
  have hVpos : 0<B.optimalScalarValue 1 0 := hC.trans_eq hV.symm
  let Q := B.capAt hZero K hK
  let e := B.totalCapExcess K
  have hKOld : (B.terminal:ℝ)<(K:ℝ) := by rw [hZero,NNReal.coe_zero];exact_mod_cast hK
  let K0 : ℝ≥0 := ⟨B.optimalScalarValue 1 0,hVpos.le⟩
  have hK0 : 0<K0 := hVpos
  have hCapEq : (⟨K0,hK0⟩ : {L : ℝ≥0 // 0<L})=⟨K,hK⟩ :=
    Subtype.ext (NNReal.eq (hV.trans hKC.symm))
  have hValueEq := congrArg (fun L : {L : ℝ≥0 // 0<L} =>
    (B.capAt hZero L.val L.property).optimalScalarValue 1 (B.totalCapExcess L.val)) hCapEq
  have hClip : Q.optimalScalarValue 1 e≤optimalCompetitiveRatio :=
    (hValueEq.symm.trans_le (B.reward_clipping_value_le hZero hVpos)).trans_eq hV
  have hGlobal : optimalCompetitiveRatio*(Q.expectedMaximum+e)≤Q.optimalScalarValue 1 e := by
    simpa only [one_mul] using Q.globalScalar_inequality zero_le_one (B.totalCapExcess_nonnegative K)
  have hSplit := B.expectedMaximum_eq_cap_add_expectedExcess hZero K hK
  rw [hM] at hSplit
  have hProphet := B.expectedMaximum_capExcess_le_total K hKOld
  have hLower : 1≤Q.expectedMaximum+e := by linarith only [hSplit,hProphet]
  have hUpper : Q.expectedMaximum+e≤1 := by
    apply (mul_le_mul_iff_right₀ hC).mp
    simpa only [mul_one] using hGlobal.trans hClip
  have hSum : Q.expectedMaximum+e=1 := le_antisymm hUpper hLower
  have hNew : Q.optimalScalarValue 1 e=optimalCompetitiveRatio := by
    apply le_antisymm hClip
    simpa only [hSum,mul_one] using hGlobal
  have hCapMean : Q.expectedMaximum≤optimalCompetitiveRatio :=
    (B.capAt_expectedMaximum_le hZero K hK).trans_eq hKC
  have hExcessLower : 1-optimalCompetitiveRatio≤e := by linarith only [hSum,hCapMean]
  have hExcessUpper : e≤optimalCompetitiveRatio := by
    have h := Q.waiting_le_value 1 e
    rw [hNew] at h
    simpa only [Q,capAt_terminal,NNReal.coe_zero,mul_zero,zero_add] using h
  have hExcess : 0<e := by
    have hCbound := optimalCompetitiveRatio_le_threeQuarters
    linarith only [hSum,hCapMean,hCbound]
  have hEquality : e=∫ v, Model.tailValue K (B.maximum v) ∂B.valueLaw := by linarith only [hSplit,hSum]
  exact ⟨⟨hExcessLower,hExcessUpper⟩,hExcess,hNew,hSum,hEquality⟩

end ProphetSecretary.Limiting.CountableInstance
