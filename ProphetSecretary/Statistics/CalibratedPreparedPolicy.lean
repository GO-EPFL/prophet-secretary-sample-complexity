import ProphetSecretary.Statistics.CalibratedLearnerMoments
import ProphetSecretary.Model.UniformPolicyMixture

/-!
# Executing the selected calibration point

The two interior knots select endpoint policies with a single independent
coin. At the two artificial extensions both endpoint indices coincide.
The mean of the validation curve retains its interpolation fraction even
when the executed policy is constant along an extension.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {PSeed : Type} [MeasurableSpace PSeed] [NeZero m]

noncomputable def frozenFamilyPolicy (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (j : Fin (J+1)) : Policy (PolicyQueryArray n J PSeed) n where
  decide r t i x H := (numericalFamilyPolicy zlo zhi estimate j).decide (q,r) t i x H

lemma frozenFamilyPolicy_isMeasurable (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (q : Reservoir n m) (j : Fin (J+1)) : (frozenFamilyPolicy zlo zhi estimate q j).IsMeasurable := by
  let Ω := PolicyQueryArray n J PSeed × (ℝ × (Fin n × (ℝ × History n)))
  have hInput : Measurable (fun p : Ω => ((q,p.1),p.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  change Measurable (fun p : Ω => (numericalFamilyPolicy zlo zhi estimate j).decide (q,p.1)
    p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  have h := (numericalFamilyPolicy_isMeasurable zlo zhi estimate he j).comp hInput
  simpa only [Function.comp_def] using h

noncomputable def preparedPolicy (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (p : PreparedCalibration n m) : Policy (PolicyQueryArray n J PSeed × ℝ) n :=
  (frozenFamilyPolicy zlo zhi estimate p.1 (lowerPolicyIndex J p.2.1)).uniformMix
    (frozenFamilyPolicy zlo zhi estimate p.1 (upperPolicyIndex J p.2.1)) p.2.2

lemma preparedPolicy_isMeasurable (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (p : PreparedCalibration n m) : (preparedPolicy (J := J) zlo zhi estimate p).IsMeasurable :=
  Policy.uniformMix_isMeasurable _ _
    (frozenFamilyPolicy_isMeasurable zlo zhi estimate he _ _)
    (frozenFamilyPolicy_isMeasurable zlo zhi estimate he _ _) _

omit [MeasurableSpace PSeed] in
lemma preparedPolicy_decide (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (p : PreparedCalibration n m) (r : PolicyQueryArray n J PSeed) (coin t : ℝ)
    (i : Fin n) (x : ℝ) (H : History n) :
    (preparedPolicy zlo zhi estimate p).decide (r,coin) t i x H =
      decidePrepared zlo zhi estimate p r coin t i x H := by
  by_cases hc : coin < p.2.2 <;>
    simp only [preparedPolicy,Policy.uniformMix,frozenFamilyPolicy,decidePrepared,mixturePolicyIndex,hc,if_true,if_false]

/-- The coefficient used to analyze a selected point, with zero on the left extension. -/
noncomputable def selectedCoefficient (zlo zhi : ℝ) (J : ℕ) (p : ℕ × ℝ) : ℝ :=
  if p.1 = 1 then 0 else
    (1-p.2)*familyCoefficient zlo zhi J (lowerPolicyIndex J p.1).val+
      p.2*familyCoefficient zlo zhi J (upperPolicyIndex J p.1).val

lemma lowerPolicyIndex_first (J : ℕ) : lowerPolicyIndex J 1 = 0 := by
  apply Fin.ext
  simp [lowerPolicyIndex]

lemma upperPolicyIndex_first (J : ℕ) : upperPolicyIndex J 1 = 0 := by
  apply Fin.ext
  simp [upperPolicyIndex]

lemma lowerPolicyIndex_last (J : ℕ) : lowerPolicyIndex J (J+2) = Fin.last J := by
  apply Fin.ext
  simp [lowerPolicyIndex]

lemma upperPolicyIndex_last (J : ℕ) : upperPolicyIndex J (J+2) = Fin.last J := by
  apply Fin.ext
  simp only [upperPolicyIndex,Fin.val_last]
  omega

omit [MeasurableSpace PSeed] in
lemma profileCurve_selected_segment (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed))
    {k : ℕ} (hk0 : 1 ≤ k) (hk1 : k ≤ J+2) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    profileCurve zlo zhi estimate q ω ((((k-1 : ℕ) : ℝ)+α)/(J+2 : ℕ)) =
      (1-α)*durationKnots (validationDuration zlo zhi estimate q ω) (k-1)+
        α*durationKnots (validationDuration zlo zhi estimate q ω) k := by
  unfold profileCurve
  have h := durationCurve_on_segment (J+2) (by omega)
    (durationKnots (validationDuration zlo zhi estimate q ω)) (k-1) (by omega) hα
  rwa [show k-1+1=k by omega] at h

lemma durationKnots_lower_eq (τ : Fin (J+1) → ℝ) {k : ℕ} (hk : 2 ≤ k) (hK : k ≤ J+2) :
    durationKnots τ (k-1) = τ (lowerPolicyIndex J k) := by
  rw [durationKnots,if_neg (by omega),dif_pos (by omega)]
  congr 1
  apply Fin.ext
  simp only [lowerPolicyIndex]
  omega

lemma durationKnots_upper_eq (τ : Fin (J+1) → ℝ) {k : ℕ} (hk : 1 ≤ k) (hK : k ≤ J+1) :
    durationKnots τ k = τ (upperPolicyIndex J k) := by
  rw [durationKnots,if_neg (by omega),dif_pos hK]
  congr 1
  apply Fin.ext
  simp only [upperPolicyIndex]
  omega

/-- At the two extensions the surrogate moves although the executed policy is fixed. -/
theorem preparedPolicy_duration_comparison (P : Instance n)
    (νP : Measure PSeed) [IsProbabilityMeasure νP] (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (q : Reservoir n m) {k : ℕ} (hk0 : 1 ≤ k) (hk1 : k ≤ J+2)
    {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    let T := (preparedPolicy zlo zhi estimate (q,k,α)).meanDuration P
      ((policyQueryArrayLaw (n := n) (J := J) νP).prod Instance.uniformClock)
    let U := ∫ ω : World n (PolicyQueryArray n J PSeed),
      profileCurve zlo zhi estimate q ω ((((k-1 : ℕ) : ℝ)+α)/(J+2 : ℕ))
        ∂P.worldLaw (policyQueryArrayLaw νP)
    (k=1 → U≤T) ∧ (2≤k → k≤J+1 → U=T) ∧ (k=J+2 → T≤U) := by
  let ν := policyQueryArrayLaw (n := n) (J := J) νP
  let a := frozenFamilyPolicy zlo zhi estimate q (lowerPolicyIndex J k)
  let b := frozenFamilyPolicy zlo zhi estimate q (upperPolicyIndex J k)
  have ha : a.IsMeasurable := frozenFamilyPolicy_isMeasurable zlo zhi estimate he _ _
  have hb : b.IsMeasurable := frozenFamilyPolicy_isMeasurable zlo zhi estimate he _ _
  let A := fun ω : World n (PolicyQueryArray n J PSeed) => a.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
  let B := fun ω : World n (PolicyQueryArray n J PSeed) => b.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
  let F := fun ω : World n (PolicyQueryArray n J PSeed) =>
    profileCurve zlo zhi estimate q ω ((((k-1 : ℕ) : ℝ)+α)/(J+2 : ℕ))
  have hT : (preparedPolicy zlo zhi estimate (q,k,α)).meanDuration P (ν.prod Instance.uniformClock) =
      ∫ ω, ((1-α)*A ω+α*B ω) ∂P.worldLaw ν := by
    have hAI : Integrable A (P.worldLaw ν) := P.integrable_worldTime ν a ha _
    have hBI : Integrable B (P.worldLaw ν) := P.integrable_worldTime ν b hb _
    rw [integral_add (hAI.const_mul _) (hBI.const_mul _),integral_const_mul,integral_const_mul]
    exact a.uniformMix_meanDuration b ha hb P ν hα
  have hF : Integrable F (P.worldLaw ν) := by
    apply Integrable.of_bound (measurable_profileCurve zlo zhi estimate he
      (y := fun _ : World n (PolicyQueryArray n J PSeed) => q) (ω := id)
      (θ := fun _ => ((((k-1 : ℕ) : ℝ)+α)/(J+2 : ℕ))) measurable_const measurable_id measurable_const).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω => by
      have h0 : 0≤F ω := by
        rw [show F ω = (1-α)*durationKnots (validationDuration zlo zhi estimate q ω) (k-1)+
          α*durationKnots (validationDuration zlo zhi estimate q ω) k from
            profileCurve_selected_segment zlo zhi estimate q ω hk0 hk1 hα]
        exact add_nonneg
          (mul_nonneg (sub_nonneg.mpr hα.2) (durationKnots_range _ (validationDuration_range zlo zhi estimate q ω) _).1)
          (mul_nonneg hα.1 (durationKnots_range _ (validationDuration_range zlo zhi estimate q ω) _).1)
      change ‖F ω‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg h0]
      rw [show F ω = (1-α)*durationKnots (validationDuration zlo zhi estimate q ω) (k-1)+
        α*durationKnots (validationDuration zlo zhi estimate q ω) k from
          profileCurve_selected_segment zlo zhi estimate q ω hk0 hk1 hα]
      nlinarith [mul_le_mul_of_nonneg_left (durationKnots_range _ (validationDuration_range zlo zhi estimate q ω) (k-1)).2
          (sub_nonneg.mpr hα.2),
        mul_le_mul_of_nonneg_left (durationKnots_range _ (validationDuration_range zlo zhi estimate q ω) k).2 hα.1]
  have hI : Integrable (fun ω => (1-α)*A ω+α*B ω) (P.worldLaw ν) :=
    ((P.integrable_worldTime ν a ha Finset.univ).const_mul _).add
      ((P.integrable_worldTime ν b hb Finset.univ).const_mul _)
  have hProfile : ∀ᵐ ω ∂P.worldLaw ν,
      let τ := validationDuration zlo zhi estimate q ω
      F ω = (1-α)*durationKnots τ (k-1)+α*durationKnots τ k ∧
      A ω=τ (lowerPolicyIndex J k) ∧ B ω=τ (upperPolicyIndex J k) := by
    filter_upwards [P.world_clocks_mem_unitInterval ν] with ω hu
    exact ⟨profileCurve_selected_segment zlo zhi estimate q ω hk0 hk1 hα,
      (validationDuration_eq_actual zlo zhi estimate q ω _ hu).symm,
      (validationDuration_eq_actual zlo zhi estimate q ω _ hu).symm⟩
  change (k=1 → (∫ ω, F ω ∂P.worldLaw ν)≤_) ∧
    (2≤k → k≤J+1 → (∫ ω, F ω ∂P.worldLaw ν)=_) ∧
    (k=J+2 → _≤(∫ ω, F ω ∂P.worldLaw ν))
  rw [hT]
  refine ⟨?_,?_,?_⟩
  · intro hk
    apply integral_mono_ae hF hI
    filter_upwards [hProfile] with ω ⟨hFω,hAω,hBω⟩
    rw [hFω,hAω,hBω,hk,durationKnots_zero,durationKnots_upper_eq _ (by omega) (by omega),
      lowerPolicyIndex_first,upperPolicyIndex_first]
    have hτ := (validationDuration_range zlo zhi estimate q ω 0).1
    nlinarith [mul_nonneg (sub_nonneg.mpr hα.2) hτ]
  · intro hk hK
    apply integral_congr_ae
    filter_upwards [hProfile] with ω ⟨hFω,hAω,hBω⟩
    rw [hFω,hAω,hBω,durationKnots_lower_eq _ hk hk1,durationKnots_upper_eq _ hk0 hK]
  · intro hk
    apply integral_mono_ae hI hF
    filter_upwards [hProfile] with ω ⟨hFω,hAω,hBω⟩
    rw [hFω,hAω,hBω,durationKnots_lower_eq _ (by omega) hk1,hk,durationKnots_last,
      lowerPolicyIndex_last,upperPolicyIndex_last]
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      (validationDuration_range zlo zhi estimate q ω (Fin.last J)).2 hα.1) _

end ProphetSecretary.Statistics.Calibration
