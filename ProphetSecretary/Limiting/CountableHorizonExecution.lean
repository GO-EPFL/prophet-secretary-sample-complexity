import ProphetSecretary.Limiting.CountableTimeScaling
import ProphetSecretary.Limiting.FirstAcceptanceTimeScaling
import ProphetSecretary.Limiting.CountableSelection
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Physical-horizon countable executions

A physical callback is transported to unit time by scaling the current clock
and the entire observed past. The anonymous history remains a past counting
measure, with no band or future-count observation. Actual accepted codes,
first selection, reward and duration are transported explicitly. The physical
terminal convention is the positive horizon, not time one.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

noncomputable def CountableRule.onUnitHorizon (π : CountableRule Seed) (h : ℝ) : CountableRule Seed where
  individual r t i x H M := π.individual r (h*t) i x (scaleIndividualHistory h H) (M.map (scalePointTime h))
  poisson r t x H M := π.poisson r (h*t) x (scaleIndividualHistory h H) (M.map (scalePointTime h))

def CountableRule.codeAcceptedAt (π : CountableRule Seed) (h : ℝ) (v : CompleteWorld Seed) (k : ℕ) : Prop :=
  codePresent v k ∧ codeTime v k ∈ Icc (0 : ℝ) h ∧ π.candidateAction v (candidateEnumeration.symm k)=true

noncomputable def CountableRule.realizedDurationAt (π : CountableRule Seed) (h : ℝ) : CompleteWorld Seed → ℝ :=
  FirstAcceptance.stoppingTimeAt h (π.codeAcceptedAt h) codeTime

noncomputable def CountableRule.realizedRewardAt (π : CountableRule Seed) (a h : ℝ) : CompleteWorld Seed → ℝ :=
  FirstAcceptance.reward a (π.codeAcceptedAt h) codeTime codeValue

def CountableRule.SelectsIndividualAt (π : CountableRule Seed) (h : ℝ) (v : CompleteWorld Seed) (i : ℕ) : Prop :=
  FirstAcceptance.Earliest (π.codeAcceptedAt h) codeTime v (candidateEnumeration (Sum.inl i))

lemma scaleClock_mem_Icc_iff {h : ℝ} (hh : 0 < h) (t : ℝ) :
    h*t ∈ Icc (0 : ℝ) h ↔ t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rintro ⟨h0,h1⟩
    constructor <;> nlinarith
  · rintro ⟨h0,h1⟩
    exact ⟨mul_nonneg hh.le h0,by nlinarith⟩

lemma codeTime_scaleCompleteTime (h : ℝ) (v : CompleteWorld Seed) (k : ℕ) (hk : codePresent v k) :
    codeTime (scaleCompleteTime h v) k=h*codeTime v k :=
  congrArg Prod.fst (candidatePoint_scaleCompleteTime h v (candidateEnumeration.symm k) hk)

lemma codeValue_scaleCompleteTime (h : ℝ) (v : CompleteWorld Seed) (k : ℕ) (hk : codePresent v k) :
    codeValue (scaleCompleteTime h v) k=codeValue v k := by
  have hValue := congrArg (fun p : Point => p.2) (candidatePoint_scaleCompleteTime h v (candidateEnumeration.symm k) hk)
  exact hValue

lemma CountableRule.candidateAction_onUnitHorizon (π : CountableRule Seed) {h : ℝ} (hh : 0 < h)
    (v : CompleteWorld Seed) (c : Candidate) (hc : candidatePresent v c) :
    (π.onUnitHorizon h).candidateAction v c=π.candidateAction (scaleCompleteTime h v) c := by
  have hPoint := candidatePoint_scaleCompleteTime h v c hc
  have hH := (scaleIndividualHistory_history hh v.2.1 v.2.2.1 (candidatePoint v c).1).symm
  have hM := anonymousHistory_scaleCompleteTime hh v (candidatePoint v c).1
  unfold CountableRule.candidateAction
  dsimp only [CountableRule.onUnitHorizon,scaleCompleteTime] at hPoint hM ⊢
  rw [hPoint]
  dsimp only [scalePointTime]
  rw [hH,hM]

lemma CountableRule.codeAccepted_onUnitHorizon (π : CountableRule Seed) {h : ℝ} (hh : 0 < h)
    (v : CompleteWorld Seed) (k : ℕ) :
    π.codeAcceptedAt h (scaleCompleteTime h v) k ↔ (π.onUnitHorizon h).codeAccepted v k := by
  have hPresent : codePresent (scaleCompleteTime h v) k ↔ codePresent v k :=
    candidatePresent_scaleCompleteTime h v _
  constructor
  · rintro ⟨hp,ht,hAction⟩
    have hp' := hPresent.mp hp
    have hTime := codeTime_scaleCompleteTime h v k hp'
    refine ⟨hp',?_,?_⟩
    · rw [hTime] at ht
      exact (scaleClock_mem_Icc_iff hh _).mp ht
    · exact (π.candidateAction_onUnitHorizon hh v _ hp').trans hAction
  · rintro ⟨hp,ht,hAction⟩
    refine ⟨hPresent.mpr hp,?_,?_⟩
    · rw [codeTime_scaleCompleteTime h v k hp]
      exact (scaleClock_mem_Icc_iff hh _).mpr ht
    · exact (π.candidateAction_onUnitHorizon hh v _ hp).symm.trans hAction

lemma CountableRule.firstAcceptance_onUnitHorizon (π : CountableRule Seed) {h : ℝ} (hh : 0 < h)
    (v : CompleteWorld Seed) :
    FirstAcceptance.HasFirstIfAccepted (π.codeAcceptedAt h) codeTime (scaleCompleteTime h v) ↔
      FirstAcceptance.HasFirstIfAccepted (π.onUnitHorizon h).codeAccepted codeTime v :=
  FirstAcceptance.hasFirstIfAccepted_timeScale_iff hh (π.codeAccepted_onUnitHorizon hh v)
    (fun k hk => codeTime_scaleCompleteTime h v k hk.1)

lemma CountableRule.durationAt_scale (π : CountableRule Seed) {h : ℝ} (hh : 0 < h) (v : CompleteWorld Seed) :
    π.realizedDurationAt h (scaleCompleteTime h v)=h*(π.onUnitHorizon h).realizedDuration v :=
  FirstAcceptance.stoppingTimeAt_timeScale hh (π.codeAccepted_onUnitHorizon hh v)
    (fun k hk => codeTime_scaleCompleteTime h v k hk.1)

lemma CountableRule.rewardAt_scale (π : CountableRule Seed) (a : ℝ) {h : ℝ} (hh : 0 < h) (v : CompleteWorld Seed) :
    π.realizedRewardAt a h (scaleCompleteTime h v)=(π.onUnitHorizon h).realizedReward a v :=
  FirstAcceptance.reward_timeScale a hh (π.codeAccepted_onUnitHorizon hh v)
    (fun k hk => codeTime_scaleCompleteTime h v k hk.1) (fun k hk => codeValue_scaleCompleteTime h v k hk.1)

lemma CountableRule.selectsIndividualAt_scale (π : CountableRule Seed) {h : ℝ} (hh : 0 < h)
    (v : CompleteWorld Seed) (i : ℕ) :
    π.SelectsIndividualAt h (scaleCompleteTime h v) i ↔ (π.onUnitHorizon h).SelectsIndividual v i :=
  FirstAcceptance.earliest_timeScale_iff hh (π.codeAccepted_onUnitHorizon hh v)
    (fun k hk => codeTime_scaleCompleteTime h v k hk.1) _

lemma CountableRule.reachesIndividualAt_scale (π : CountableRule Seed) {h : ℝ} (hh : 0 < h)
    (v : CompleteWorld Seed) (i : ℕ) :
    (scaleCompleteTime h v).2.2.1 i ≤ π.realizedDurationAt h (scaleCompleteTime h v) ↔
      v.2.2.1 i ≤ (π.onUnitHorizon h).realizedDuration v := by
  rw [π.durationAt_scale hh]
  exact mul_le_mul_iff_right₀ hh

variable [MeasurableSpace Seed]

lemma CountableRule.onUnitHorizon_isMeasurable (π : CountableRule Seed) (hπ : π.IsMeasurable) (h : ℝ) :
    (π.onUnitHorizon h).IsMeasurable := by
  have hMap := Measure.measurable_map (scalePointTime h) (measurable_scalePointTime h)
  constructor
  · let Ω := Seed × (ℝ × (ℕ × (ℝ × (IndividualHistory × Measure Point))))
    have hr : Measurable (fun z : Ω => z.1) := measurable_fst
    have ht : Measurable (fun z : Ω => h*z.2.1) := by fun_prop
    have hi : Measurable (fun z : Ω => z.2.2.1) := by fun_prop
    have hx : Measurable (fun z : Ω => z.2.2.2.1) := by fun_prop
    have hH : Measurable (fun z : Ω => scaleIndividualHistory h z.2.2.2.2.1) :=
      (measurable_scaleIndividualHistory h).comp (by fun_prop)
    have hM : Measurable (fun z : Ω => z.2.2.2.2.2.map (scalePointTime h)) := hMap.comp (by fun_prop)
    exact hπ.1.comp (hr.prodMk (ht.prodMk (hi.prodMk (hx.prodMk (hH.prodMk hM)))))
  · let Ω := Seed × (Point × (IndividualHistory × Measure Point))
    have hr : Measurable (fun z : Ω => z.1) := measurable_fst
    have ht : Measurable (fun z : Ω => h*z.2.1.1) := by fun_prop
    have hx : Measurable (fun z : Ω => z.2.1.2) := by fun_prop
    have hH : Measurable (fun z : Ω => scaleIndividualHistory h z.2.2.1) :=
      (measurable_scaleIndividualHistory h).comp (by fun_prop)
    have hM : Measurable (fun z : Ω => z.2.2.2.map (scalePointTime h)) := hMap.comp (by fun_prop)
    exact hπ.2.comp (hr.prodMk ((ht.prodMk hx).prodMk (hH.prodMk hM)))

lemma CountableRule.measurableSet_codeAcceptedAt (π : CountableRule Seed) (hπ : π.IsMeasurable) (h : ℝ) (k : ℕ) :
    MeasurableSet {v | π.codeAcceptedAt h v k} :=
  (measurableSet_codePresent k).inter (((measurable_codeTime k) measurableSet_Icc).inter
    ((π.measurable_candidateAction hπ _) (measurableSet_singleton true)))

lemma CountableRule.measurable_realizedDurationAt (π : CountableRule Seed) (hπ : π.IsMeasurable) (h : ℝ) :
    Measurable (π.realizedDurationAt h) :=
  FirstAcceptance.measurable_stoppingTimeAt h (π.measurableSet_codeAcceptedAt hπ h) measurable_codeTime

lemma CountableRule.measurable_realizedRewardAt (π : CountableRule Seed) (hπ : π.IsMeasurable) (a h : ℝ) :
    Measurable (π.realizedRewardAt a h) :=
  FirstAcceptance.measurable_reward a (π.measurableSet_codeAcceptedAt hπ h) measurable_codeTime measurable_codeValue

end ProphetSecretary.Limiting.CountableInstance
