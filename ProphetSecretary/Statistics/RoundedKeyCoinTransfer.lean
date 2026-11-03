import ProphetSecretary.Statistics.RankCalibrationFailure
import ProphetSecretary.Model.RankOutcomeAgreement
import ProphetSecretary.Model.RankToClockLaw

/-!
# Transfer to rounded validation keys and an independent finite coin

The actual rank learner uses its rounded permutations and mixture coin.
On the common key and coin coupling, its complete rank execution agrees
with the ideal rounded-clock learner outside the two measured error events.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m]

lemma integral_unit_loss_of_agreement {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {E : Set Ω} (hE : MeasurableSet E) {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hUnit : ∀ᵐ ω ∂μ, f ω≤1 ∧ 0≤g ω)
    (hEq : ∀ᵐ ω ∂μ, ω∉E → f ω=g ω) :
    (∫ ω,f ω ∂μ)-μ.real E≤∫ ω,g ω ∂μ := by
  let H := E.indicator (1 : Ω → ℝ)
  have hHI : Integrable H μ := (integrable_const (1 : ℝ)).indicator hE
  have h := integral_mono_ae (hf.sub hHI) hg (by
    filter_upwards [hUnit,hEq] with ω hU h
    change f ω-H ω≤g ω
    by_cases hω : ω∈E
    · rw [show H ω=1 from indicator_of_mem hω _]
      linarith only [hU.1,hU.2]
    · rw [show H ω=0 from indicator_of_notMem hω _,sub_zero,h hω])
  change (∫ ω,f ω-H ω ∂μ)≤∫ ω,g ω ∂μ at h
  rw [integral_sub (f := f) (g := H) hf hHI,show (∫ ω,H ω ∂μ)=μ.real E from integral_indicator_one hE] at h
  exact h

section

variable (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
  [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
  (times : Measure (Fin n → ℝ)) [IsProbabilityMeasure times]
  {N Q : ℕ} (hN : 0<N) (hQ : 0<Q)
  (mu zlo zhi : ℝ) (targetEstimate : TargetEstimator n m TSeed)
  (policyEstimate : ContinuationEstimator n m PSeed)
  (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
  (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
    policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))

local notation "D" => RankCoupledData n m J TSeed PSeed
local notation "U" => (Fin n → ℝ) × (Equiv.Perm (Fin n) × D)
local notation "I" => rankCalibratedLearner (J := J) νT νP (Instance.uniformPermutationLaw n) times Instance.uniformClock
  id measurable_id mu zlo zhi targetEstimate policyEstimate hT hC
local notation "f" => uniformGridRound Q hQ
local notation "g" => roundedValidationPermutation hN
local notation "ord" => Measure.map g (Instance.clocksLaw n)
local notation "coin" => Measure.map f Instance.uniformClock

local instance roundedOrder_probability : IsProbabilityMeasure ord :=
  Measure.isProbabilityMeasure_map (measurable_roundedValidationPermutation n N hN).aemeasurable
local instance roundedCoin_probability : IsProbabilityMeasure coin :=
  Measure.isProbabilityMeasure_map (measurable_uniformGridRound Q hQ).aemeasurable

local notation "A" => rankCalibratedLearner (J := J) νT νP ord times coin
  f (measurable_uniformGridRound Q hQ) mu zlo zhi targetEstimate policyEstimate hT hC
local notation "α" => coupledIdealMixture (J := J) mu zlo zhi targetEstimate policyEstimate
local notation "μ" => Measure.prod (P.reservoirLaw (2*m)) (rankCalibrationCoupledSeedLaw (n := n) (m := m) (J := J) νT νP times)
local notation "W" => Measure.prod P.valuesLaw (Measure.prod (Instance.uniformPermutationLaw n) μ)

private def liftRankProjection
    (order : (Fin n → ℝ) → Equiv.Perm (Fin n)) (draw : ℝ → ℝ) (w : U) :
    (Fin n → ℝ) × (Equiv.Perm (Fin n) × (Reservoir n (2*m) × RankCalibratedSeed n m J TSeed PSeed)) :=
  (w.1,w.2.1,w.2.2.1,projectRankCalibrationSeed order draw w.2.2.2)

local notation "uI" => liftRankProjection (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed)
  Instance.arrivalPermutation id
local notation "uA" => liftRankProjection (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed) g f

omit [NeZero m] in
private lemma liftRankProjection_measurePreserving
    {order : (Fin n → ℝ) → Equiv.Perm (Fin n)} {draw : ℝ → ℝ}
    {μ₁ : Measure (RankCalibrationCoupledSeed n m J TSeed PSeed)}
    {μ₂ : Measure (RankCalibratedSeed n m J TSeed PSeed)}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h : MeasurePreserving (projectRankCalibrationSeed order draw) μ₁ μ₂) :
    MeasurePreserving (liftRankProjection order draw)
      (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ((P.reservoirLaw (2*m)).prod μ₁)))
      (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ((P.reservoirLaw (2*m)).prod μ₂))) := by
  let T := P.reservoirLaw (2*m)
  haveI : IsProbabilityMeasure T := P.reservoirLaw_probability (2*m)
  exact (MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Instance.uniformPermutationLaw n)).prod
    ((MeasurePreserving.id T).prod h))

private lemma uI_measurePreserving : MeasurePreserving uI W (((I).randomizedPolicy P).worldLaw P) := by
  have h := projectRankCalibrationSeed_measurePreserving (m := m) (J := J) νT νP times
    Instance.measurable_arrivalPermutation measurable_id
  rw [Instance.arrivalPermutation_map,Measure.map_id] at h
  let ν := rankCalibratedSeedLaw (n := n) (m := m) (J := J) νT νP
    (Instance.uniformPermutationLaw n) times Instance.uniformClock
  haveI : IsProbabilityMeasure ν := rankCalibratedSeedLaw_probability νT νP
    (Instance.uniformPermutationLaw n) times Instance.uniformClock
  exact liftRankProjection_measurePreserving P (μ₂ := ν) h

private lemma uA_measurePreserving : MeasurePreserving uA W (((A).randomizedPolicy P).worldLaw P) := by
  let ν := rankCalibratedSeedLaw (n := n) (m := m) (J := J) νT νP ord times coin
  haveI : IsProbabilityMeasure ν := rankCalibratedSeedLaw_probability νT νP ord times coin
  exact liftRankProjection_measurePreserving P (μ₂ := ν)
    (projectRankCalibrationSeed_measurePreserving νT νP times
      (measurable_roundedValidationPermutation n N hN) (measurable_uniformGridRound Q hQ))

private def rawFailure : Set D :=
  {p | validationOrderFailure hN p} ∪
    {p | mixtureGridFailure Q hQ (α (coupledCalibrationOfflineCoin p).1) p.2.2.2.2.2}

include hT hC in
private lemma measurableSet_rawFailure : MeasurableSet (rawFailure (J := J) hN hQ mu zlo zhi targetEstimate policyEstimate) := by
  have hα := measurable_coupledIdealMixture (J := J) mu zlo zhi targetEstimate policyEstimate hT hC
  have hp : Measurable (coupledCalibrationOfflineCoin (m := m) (J := J) (n := n) (TSeed := TSeed) (PSeed := PSeed)) := by
    unfold coupledCalibrationOfflineCoin
    fun_prop
  have hCoin : Measurable (fun p : D => p.2.2.2.2.2) := by fun_prop
  have hAlpha : Measurable (fun p : D => α (coupledCalibrationOfflineCoin p).1) :=
    hα.comp (measurable_fst.comp hp)
  exact (measurableSet_validationOrderFailure hN).union
    (measurableSet_mixtureGridFailure Q hQ hAlpha hCoin)

local notation "F" => rawFailure (J := J) hN hQ mu zlo zhi targetEstimate policyEstimate

include hT hC in
private lemma rawFailure_probability_le :
    (μ).real F≤(m : ℝ)*((n : ℝ)*((n : ℝ)-1))/(2*(N : ℝ))+1/(Q : ℝ) := by
  exact (measureReal_union_le _ _).trans (add_le_add
    (validationOrderFailure_probability_le (m := m) (J := J) P νT νP times hN)
    (mixtureGridFailure_probability_le P νT νP times Q hQ α
      (measurable_coupledIdealMixture mu zlo zhi targetEstimate policyEstimate hT hC)
      (coupledIdealMixture_range mu zlo zhi targetEstimate policyEstimate)))

private lemma actions_agree_off_rawFailure (ω : U) (hω : ω.2.2∉F) (i : Fin n) :
    (I).policy.action (uI ω).2.2 ω.2.1 ω.1 i =
      (A).policy.action (uA ω).2.2 ω.2.1 ω.1 i := by
  let p := ω.2.2
  let dI := (p.1,projectRankCalibrationSeed Instance.arrivalPermutation id p.2)
  let dA := (p.1,projectRankCalibrationSeed g f p.2)
  have hP (j : Fin m) : g (p.2.2.1 j).1=Instance.arrivalPermutation (p.2.2.1 j).1 := by
    by_contra h
    exact hω (Or.inl ⟨j,h⟩)
  have hD : rankCalibrationData dI=rankCalibrationData dA := by
    let v := trainingAndValidation p.1
    have he : (fun j : Fin m => (v.2 j,Instance.arrivalPermutation (p.2.2.1 j).1,(p.2.2.1 j).2)) =
        (fun j : Fin m => (v.2 j,g (p.2.2.1 j).1,(p.2.2.1 j).2)) :=
      funext (fun j => by rw [hP j])
    exact congrArg (fun t => ((v.1,p.2.1),t)) he
  let a := rankValidationPrepare mu zlo zhi targetEstimate policyEstimate (rankCalibrationData dI)
  have ha : rankValidationPrepare mu zlo zhi targetEstimate policyEstimate (rankCalibrationData dA)=a :=
    congrArg (rankValidationPrepare mu zlo zhi targetEstimate policyEstimate) hD.symm
  have hc : decide (p.2.2.2.2.2<a.2.2)=decide (f p.2.2.2.2.2<f a.2.2) := by
    apply Classical.not_not.mp
    intro h
    exact hω (Or.inr h)
  have hJ : mixturePolicyIndex J a.2 p.2.2.2.2.2 =
      mixturePolicyIndex J (a.2.1,f a.2.2) (f p.2.2.2.2.2) := by
    have h := decide_eq_decide.mp hc
    by_cases h1 : p.2.2.2.2.2<a.2.2
    · simp only [mixturePolicyIndex,if_pos h1,if_pos (h.mp h1)]
    · simp only [mixturePolicyIndex,if_neg h1,if_neg (fun h2 => h1 (h.mpr h2))]
  let k := ω.2.1.symm i
  let H := rankHistory ω.2.1 ω.1 k
  let x := ω.1 i
  have hi : (I).policy.decide dI k i x H=
      (rankCalibratedSamplePolicy (J := J) id mu zlo zhi targetEstimate policyEstimate).decide dI k i x H :=
    RankLearner.ofComputedSamplePolicy_decide _ _ _ _ dI.1 dI.2 k i x H
  have hb : (A).policy.decide dA k i x H=
      (rankCalibratedSamplePolicy (J := J) f mu zlo zhi targetEstimate policyEstimate).decide dA k i x H :=
    RankLearner.ofComputedSamplePolicy_decide _ _ _ _ dA.1 dA.2 k i x H
  refine hi.trans (Eq.trans ?_ hb.symm)
  change (numericalFamilyPolicy zlo zhi policyEstimate (mixturePolicyIndex J a.2 p.2.2.2.2.2)).clockToRank.decide
      (p.2.2.2.1,a.1,p.2.2.2.2.1) _ i _ _ =
    (numericalFamilyPolicy zlo zhi policyEstimate
      (mixturePolicyIndex J ((rankValidationPrepare mu zlo zhi targetEstimate policyEstimate
        (rankCalibrationData dA)).2.1,f (rankValidationPrepare mu zlo zhi targetEstimate policyEstimate
        (rankCalibrationData dA)).2.2) (f p.2.2.2.2.2))).clockToRank.decide
      (p.2.2.2.1,(rankValidationPrepare mu zlo zhi targetEstimate policyEstimate (rankCalibrationData dA)).1,
        p.2.2.2.2.1) _ i _ _
  rw [ha,hJ]

omit [NeZero m] in
private lemma rankWorld_valueBound (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) :
    ∀ᵐ w : U ∂W, (∀ i, 0≤w.1 i) ∧ (∀ i,w.1 i≤1) := by
  have hV : MeasurePreserving (fun w : U => w.1) W P.valuesLaw := measurePreserving_fst
  have hc : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i≤1 := by
    simp only [ae_all_iff]
    intro i
    exact (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hcap i)
  filter_upwards [hV.quasiMeasurePreserving.ae P.ae_nonnegative,hV.quasiMeasurePreserving.ae hc] with _ h1 h2
  exact ⟨h1,h2⟩

include hT hC in
private lemma rankWorld_failure_measure :
    (W).real {ω : U | ω.2.2∈F}=(μ).real F := by
  have h : MeasurePreserving (fun ω : U => ω.2.2) W μ :=
    measurePreserving_snd.comp measurePreserving_snd
  exact congrArg ENNReal.toReal (h.measure_preimage
    (measurableSet_rawFailure hN hQ mu zlo zhi targetEstimate policyEstimate hT hC).nullMeasurableSet)

/-- Rounded validation permutations and coin reduce expected reward by at most their total error. -/
theorem roundedKeysCoin_expectedReward (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) :
    (I).expectedReward P-((m : ℝ)*((n : ℝ)*((n : ℝ)-1))/(2*(N : ℝ))+1/(Q : ℝ)) ≤
      (A).expectedReward P := by
  let π := (I).randomizedPolicy P
  let σ := (A).randomizedPolicy P
  let v := π.realizedReward ∘ uI
  let w := σ.realizedReward ∘ uA
  let E := {ω : U | ω.2.2∈F}
  have hE : MeasurableSet E := (measurableSet_rawFailure hN hQ mu zlo zhi
    targetEstimate policyEstimate hT hC).preimage (measurable_snd.comp measurable_snd)
  have h1 := uI_measurePreserving (J := J) P νT νP times mu zlo zhi targetEstimate policyEstimate hT hC
  have h2 := uA_measurePreserving (J := J) P νT νP times hN hQ mu zlo zhi targetEstimate policyEstimate hT hC
  have hP := P.integrable_maximum_of_bounded hcap
  have hV : Integrable v W := h1.integrable_comp_of_integrable (π.integrable_realizedReward P hP)
  have hW : Integrable w W := h2.integrable_comp_of_integrable (σ.integrable_realizedReward P hP)
  have hB : ∀ᵐ ω ∂W, v ω≤1 ∧ 0≤w ω := by
    filter_upwards [rankWorld_valueBound (m := m) (J := J) P νT νP times hcap] with ω hω
    exact ⟨(π.rule.reward_le_maximum _ _ _).trans (Instance.maximum_le ω.1 zero_le_one hω.2),
      σ.rule.reward_nonnegative _ _ _ hω.1⟩
  have hEq : ∀ᵐ ω ∂W, ω∉E → v ω=w ω := Filter.Eventually.of_forall fun ω hω =>
    RankPolicy.reward_eq_of_actions_eq _ _ _ _ _ _
      (actions_agree_off_rawFailure νT νP times hN hQ mu zlo zhi targetEstimate policyEstimate hT hC ω hω)
  have h := integral_unit_loss_of_agreement W hE hV hW hB hEq
  rw [rankWorld_failure_measure P νT νP times hN hQ mu zlo zhi targetEstimate policyEstimate hT hC] at h
  have hI : (∫ ω,v ω ∂W)=(I).expectedReward P :=
    h1.hasLaw.integral_comp (π.integrable_realizedReward P hP).aestronglyMeasurable
  have hA : (∫ ω,w ω ∂W)=(A).expectedReward P :=
    h2.hasLaw.integral_comp (σ.integrable_realizedReward P hP).aestronglyMeasurable
  rw [hI,hA] at h
  exact (sub_le_sub_left (rawFailure_probability_le P νT νP times hN hQ mu zlo zhi targetEstimate policyEstimate hT hC) _).trans h


private noncomputable def reachValue (π : RandomizedRankPolicy n) (i : Fin n) (ω : π.World) : ℝ :=
  if π.rule.Reaches ω.2.2 ω.2.1 ω.1 i then 1 else 0

private lemma reachValue_integrable (π : RandomizedRankPolicy n) (i : Fin n) :
    Integrable (reachValue π i) (π.worldLaw P) :=
  (integrable_const (1 : ℝ)).indicator (π.rule.measurableSet_reaches π.measurable_rule
    (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst) i)

private lemma reachValue_integral (π : RandomizedRankPolicy n) (i : Fin n) :
    (∫ ω,reachValue π i ω ∂π.worldLaw P)=π.reachProbability P i :=
  integral_indicator_one (π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
    (measurable_fst.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst) i)

/-- The same finite-grid transfer holds for each identity's actual reach. -/
theorem roundedKeysCoin_reachProbability (i : Fin n) :
    (I).reachProbability P i-((m : ℝ)*((n : ℝ)*((n : ℝ)-1))/(2*(N : ℝ))+1/(Q : ℝ)) ≤
      (A).reachProbability P i := by
  let π := (I).randomizedPolicy P
  let σ := (A).randomizedPolicy P
  let v := reachValue π i ∘ uI
  let w := reachValue σ i ∘ uA
  let E := {ω : U | ω.2.2∈F}
  have hE : MeasurableSet E := (measurableSet_rawFailure hN hQ mu zlo zhi
    targetEstimate policyEstimate hT hC).preimage (measurable_snd.comp measurable_snd)
  have h1 := uI_measurePreserving (J := J) P νT νP times mu zlo zhi targetEstimate policyEstimate hT hC
  have h2 := uA_measurePreserving (J := J) P νT νP times hN hQ mu zlo zhi targetEstimate policyEstimate hT hC
  have hV : Integrable v W := h1.integrable_comp_of_integrable (reachValue_integrable P π i)
  have hW : Integrable w W := h2.integrable_comp_of_integrable (reachValue_integrable P σ i)
  have hB : ∀ᵐ ω ∂W, v ω≤1 ∧ 0≤w ω := Filter.Eventually.of_forall fun ω => by
    simp only [v,w,Function.comp_def,reachValue]
    constructor <;> split_ifs <;> norm_num
  have hEq : ∀ᵐ ω ∂W, ω∉E → v ω=w ω := Filter.Eventually.of_forall fun ω hω => by
    have h := RankPolicy.reaches_iff_of_actions_eq _ _ _ _ _ _
      (actions_agree_off_rawFailure νT νP times hN hQ mu zlo zhi targetEstimate policyEstimate hT hC ω hω) i
    change (if (I).policy.Reaches (uI ω).2.2 ω.2.1 ω.1 i then (1 : ℝ) else 0) =
      (if (A).policy.Reaches (uA ω).2.2 ω.2.1 ω.1 i then (1 : ℝ) else 0)
    simp only [h]
  have h := integral_unit_loss_of_agreement W hE hV hW hB hEq
  rw [rankWorld_failure_measure P νT νP times hN hQ mu zlo zhi targetEstimate policyEstimate hT hC] at h
  have hI : (∫ ω,v ω ∂W)=(I).reachProbability P i :=
    (h1.hasLaw.integral_comp (reachValue_integrable P π i).aestronglyMeasurable).trans (reachValue_integral P π i)
  have hA : (∫ ω,w ω ∂W)=(A).reachProbability P i :=
    (h2.hasLaw.integral_comp (reachValue_integrable P σ i).aestronglyMeasurable).trans (reachValue_integral P σ i)
  rw [hI,hA] at h
  exact (sub_le_sub_left (rawFailure_probability_le P νT νP times hN hQ mu zlo zhi targetEstimate policyEstimate hT hC) _).trans h

end

end ProphetSecretary.Statistics.Calibration
