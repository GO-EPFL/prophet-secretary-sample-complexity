import ProphetSecretary.Statistics.CalibratedCoefficientGrid
import Mathlib.Probability.Moments.SubGaussian

/-!
# The right extension is rarely selected

The largest coefficient forces waiting on a small-mean instance. The
validation endpoint averages independent durations in the unit interval,
so selection of the right extension has an exponentially small probability.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators NNReal

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} [NeZero m] {PSeed : Type}

lemma frozenFamilyPolicy_reward_ge_floor {zlo zhi : ℝ} (h0 : 0≤zlo) (hz : zlo≤zhi)
    (h1 : zhi≤1) (estimate : ContinuationEstimator n m PSeed) (q : Reservoir n m)
    (j : Fin (J+1)) (r : PolicyQueryArray n J PSeed) (x u : Fin n → ℝ)
    (hx : ∀ i, 0≤x i) (hu : ∀ i, u i ∈ Icc (0 : ℝ) 1) :
    familyCoefficient zlo zhi J j.val *
      (1-(frozenFamilyPolicy zlo zhi estimate q j).stoppingTime r Finset.univ x u) ≤
        (frozenFamilyPolicy zlo zhi estimate q j).reward r Finset.univ x u := by
  let π := frozenFamilyPolicy zlo zhi estimate q j
  let z := familyCoefficient zlo zhi J j.val
  have hzR := familyCoefficient_range hz J j.val
  have hz0 : 0≤z := h0.trans hzR.1
  have hz1 : z≤1 := hzR.2.trans h1
  rcases π.stoppingTime_eq_one_or_actualSelects r Finset.univ x u with ht | ⟨i, hi⟩
  · change z*(1-π.stoppingTime r Finset.univ x u)≤π.reward r Finset.univ x u
    rw [ht,sub_self,mul_zero]
    exact π.reward_nonnegative _ _ _ _ hx
  · change z*(1-π.stoppingTime r Finset.univ x u)≤π.reward r Finset.univ x u
    rw [π.reward_eq_of_actualSelects _ _ _ _ hi,← hi.1.2]
    have ha := ((π.mem_accepted r Finset.univ x u i).mp hi.1.1).2
    have hcap : z*(1-u i)≤1 := by nlinarith [mul_nonneg hz0 (hu i).1]
    by_cases hf : familyFallback q
    · have he : x i=1 := by
        simpa only [π,Policy.action,frozenFamilyPolicy,numericalFamilyPolicy,if_pos hf,decide_eq_true_eq] using ha
      rwa [he]
    · have he : x i=1 ∨ (0<x i ∧
          familyThreshold zlo zhi estimate j (q,r) (u i) i (history Finset.univ x u (u i))≤x i) := by
        simpa only [π,Policy.action,frozenFamilyPolicy,numericalFamilyPolicy,if_neg hf,
          cappedHistoryThresholdPolicy,decide_eq_true_eq] using ha
      rcases he with hc | hh
      · rwa [hc]
      · apply le_trans _ hh.2
        rw [← unitRemaining_eq (hu i)]
        exact ProphetSecretary.Statistics.durationFloor_le_nestedContinuation
          (familyCoefficient zlo zhi J)
          (familyQuery zlo zhi estimate (q,r) (u i) i (history Finset.univ x u (u i)))
          (unitRemaining (u i)) j.val

variable [MeasurableSpace PSeed]

lemma last_validationDuration_mean_ge (P : Instance n) (νP : Measure PSeed)
    [IsProbabilityMeasure νP] (hP : Integrable Instance.maximum P.valuesLaw)
    (hM : P.expectedMaximum ≤ 1/80) {zlo : ℝ} (h0 : 0≤zlo) (hz : zlo≤1/4) (hJ : 0<J)
    (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) (q : Reservoir n m) :
    (19/20 : ℝ) ≤ ∫ ω : World n (PolicyQueryArray n J PSeed),
      validationDuration zlo (1/4) estimate q ω (Fin.last J) ∂P.worldLaw (policyQueryArrayLaw νP) := by
  let ν := policyQueryArrayLaw (n := n) (J := J) νP
  let π := frozenFamilyPolicy zlo (1/4) estimate q (Fin.last J)
  let R := RandomizedPolicy.ofRule ν π (frozenFamilyPolicy_isMeasurable zlo (1/4) estimate he q _)
  have hVal : MeasurePreserving (fun ω : World n (PolicyQueryArray n J PSeed) => ω.1) (P.worldLaw ν) P.valuesLaw :=
    measurePreserving_fst
  have hAe : ∀ᵐ ω ∂P.worldLaw ν, (1/4 : ℝ)*(1-R.realizedDuration ω) ≤ R.realizedReward ω := by
    filter_upwards [P.world_clocks_mem_unitInterval ν,hVal.quasiMeasurePreserving.ae P.ae_nonnegative] with ω hu hx
    have h := frozenFamilyPolicy_reward_ge_floor h0 hz (by norm_num : (1/4 : ℝ)≤1)
      estimate q (Fin.last J) ω.2.2 ω.1 ω.2.1 hx hu
    rw [Fin.val_last,familyCoefficient_last zlo _ hJ] at h
    exact h
  have hInt := integral_mono_ae (((integrable_const (1 : ℝ)).sub (R.integrable_realizedDuration P)).const_mul (1/4))
    (R.integrable_realizedReward P hP) hAe
  change (∫ ω, (1/4 : ℝ)*(1-R.realizedDuration ω) ∂P.worldLaw R.seedLaw) ≤
    R.expectedReward P at hInt
  rw [integral_const_mul,integral_sub (f := fun _ => (1 : ℝ)) (g := R.realizedDuration)
    (integrable_const (1 : ℝ)) (R.integrable_realizedDuration P),
    integral_const,probReal_univ,one_smul] at hInt
  have hRP := (R.expectedReward_le_maximum P hP).trans hM
  have heq : (∫ ω : World n (PolicyQueryArray n J PSeed),
      validationDuration zlo (1/4) estimate q ω (Fin.last J) ∂P.worldLaw ν)=R.expectedDuration P := by
    apply integral_congr_ae
    filter_upwards [P.world_clocks_mem_unitInterval ν] with ω hu
    exact validationDuration_eq_actual zlo (1/4) estimate q ω _ hu
  rw [heq]
  change (1/4 : ℝ)*(1-R.expectedDuration P)≤R.expectedReward P at hInt
  linarith

omit [MeasurableSpace PSeed] in
lemma validationSelection_right_implies_mean_lt (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m PSeed) (q : Reservoir n m)
    (w : Fin m → World n (PolicyQueryArray n J PSeed)) {ρ : ℝ} (hρ : ρ∈Ioc (0 : ℝ) 1)
    (hright : (validationSelection zlo zhi estimate q w ρ).1=J+2) :
    (m : ℝ)⁻¹*∑ a, validationDuration zlo zhi estimate q (w a) (Fin.last J) < ρ := by
  let v := meanDurationKnots zlo zhi estimate q w
  have h0 : v 0<ρ := by simpa only [v,meanDurationKnots_zero] using hρ.1
  have h1 : ρ≤v (J+2) := by simpa only [v,meanDurationKnots_last] using hρ.2
  have h := (calibrationCrossing_bounds v ρ (J+2) h0 h1).2.2.1
  change calibrationCrossing v ρ (J+2)=J+2 at hright
  rw [hright,show J+2-1=J+1 by omega] at h
  change (m : ℝ)⁻¹*∑ a, durationKnots (validationDuration zlo zhi estimate q (w a)) (J+1)<ρ at h
  have hEq (a : Fin m) : durationKnots (validationDuration zlo zhi estimate q (w a)) (J+1) =
      validationDuration zlo zhi estimate q (w a) (Fin.last J) := by
    rw [durationKnots_upper_eq _ (by omega) le_rfl]
    congr 1
    apply Fin.ext
    simp [upperPolicyIndex]
  simpa only [hEq] using h

private lemma unitAverage_lower_tail {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (f : Y → ℝ) (hf : Measurable f)
    (hr : ∀ y, f y ∈ Icc (0 : ℝ) 1) {δ : ℝ} (hδ : 0≤δ) :
    (Measure.pi (fun _ : Fin m => μ)).real
      {y | (m : ℝ)⁻¹*∑ i, f (y i) ≤ (∫ v,f v ∂μ)-δ} ≤ Real.exp (-2*(m : ℝ)*δ^2) := by
  let ν : Measure (Fin m → Y) := Measure.pi (fun _ => μ)
  let M := ∫ y, f y ∂μ
  let X : Fin m → (Fin m → Y) → ℝ := fun i y => M-f (y i)
  have hfI : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs,abs_of_nonneg (hr y).1]; exact (hr y).2)
  have hXi (i : Fin m) : Integrable (fun y : Fin m → Y => f (y i)) ν :=
    (measurePreserving_eval (fun _ : Fin m => μ) i).integrable_comp_of_integrable hfI
  have hmean (i : Fin m) : (∫ y : Fin m → Y, f (y i) ∂ν)=M :=
    (measurePreserving_eval (fun _ : Fin m => μ) i).hasLaw.integral_comp hf.aestronglyMeasurable
  have hsub (i : Fin m) : HasSubgaussianMGF (X i) (1/4) ν := by
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (measurable_const.sub (hf.comp (measurable_pi_apply i))).aemeasurable
      (Filter.Eventually.of_forall fun y : Fin m → Y =>
        show X i y∈Icc (M-1) M from ⟨by dsimp [X]; linarith [(hr (y i)).2],
          by dsimp [X]; linarith [(hr (y i)).1]⟩)
      (show (∫ y : Fin m → Y, M-f (y i) ∂ν)=0 by
        rw [integral_sub (integrable_const M) (hXi i),hmean,integral_const,probReal_univ,one_smul,sub_self])
    rw [show M-(M-1)=1 by ring] at h
    norm_num at h
    exact h
  have hind : iIndepFun X ν :=
    iIndepFun_pi (fun _ : Fin m => (measurable_const.sub hf).aemeasurable)
  have hTail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (c := fun _ => (1/4 : ℝ≥0)) (fun i _ => hsub i)
    (mul_nonneg (Nat.cast_nonneg m) hδ)
  have hInc : {y | (m : ℝ)⁻¹*∑ i, f (y i)≤M-δ} ⊆ {y | (m : ℝ)*δ≤∑ i : Fin m,X i y} := by
    intro y hy
    have hm : (0 : ℝ)<m := Nat.cast_pos.mpr (NeZero.pos m)
    change (m : ℝ)⁻¹*∑ i, f (y i)≤M-δ at hy
    have h := mul_le_mul_of_nonneg_left hy hm.le
    rw [← mul_assoc,mul_inv_cancel₀ hm.ne',one_mul] at h
    change (m : ℝ)*δ≤∑ i : Fin m,(M-f (y i))
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    linarith
  apply (measureReal_mono hInc).trans (hTail.trans_eq ?_)
  congr 1
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,NNReal.coe_mul,
    NNReal.coe_natCast,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one]
  have hm : (m : ℝ)≠0 := by exact_mod_cast NeZero.ne m
  field_simp [hm]
  ring

theorem validationSelection_right_probability_le (P : Instance n) (νP : Measure PSeed)
    [IsProbabilityMeasure νP] (hP : Integrable Instance.maximum P.valuesLaw)
    (hM : P.expectedMaximum≤1/80) {zlo : ℝ} (h0 : 0≤zlo) (hz : zlo≤1/4) (hJ : 0<J)
    (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) (q : Reservoir n m)
    {ρ : ℝ} (hρ : ρ∈Ioc (0 : ℝ) (4/5)) :
    (validationWorldArrayLaw (m := m) (J := J) P νP).real
      {w | (validationSelection zlo (1/4) estimate q w ρ).1=J+2} ≤ Real.exp (-9*(m : ℝ)/200) := by
  let ν := P.worldLaw (policyQueryArrayLaw (n := n) (J := J) νP)
  let f := fun ω : World n (PolicyQueryArray n J PSeed) => validationDuration zlo (1/4) estimate q ω (Fin.last J)
  have hf : Measurable f := measurable_validationDuration zlo (1/4) estimate he
    (y := fun _ => q) (ω := id) measurable_const measurable_id _
  have hMean := last_validationDuration_mean_ge P νP hP hM h0 hz hJ estimate he q
  have hR : ρ∈Ioc (0 : ℝ) 1 := ⟨hρ.1,hρ.2.trans (by norm_num)⟩
  have hInc : {w | (validationSelection zlo (1/4) estimate q w ρ).1=J+2} ⊆
      {w | (m : ℝ)⁻¹*∑ i,f (w i)≤(∫ ω,f ω ∂ν)-3/20} := by
    intro w hw
    have h := validationSelection_right_implies_mean_lt zlo (1/4) estimate q w hR hw
    change (19/20 : ℝ)≤∫ ω,f ω ∂ν at hMean
    change (m : ℝ)⁻¹*∑ i,f (w i)≤(∫ ω,f ω ∂ν)-3/20
    linarith [hρ.2]
  apply (measureReal_mono hInc).trans
  have h := unitAverage_lower_tail (m := m) ν f hf (validationDuration_range zlo (1/4) estimate q · (Fin.last J))
    (by norm_num : (0 : ℝ)≤3/20)
  simpa only [validationWorldArrayLaw,ν,show -2*(m : ℝ)*(3/20)^2 = -9*(m : ℝ)/200 by ring] using h

end ProphetSecretary.Statistics.Calibration
