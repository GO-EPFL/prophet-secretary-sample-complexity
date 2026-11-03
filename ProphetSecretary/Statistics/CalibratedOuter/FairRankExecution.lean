import ProphetSecretary.Statistics.CalibratedOuter.FairMarks
import ProphetSecretary.Model.RankLearnerToClock

/-!
# Executing the outer transform on arrival ranks

The outer transform changes only values, so it commutes with the transfer
between timestamp histories and rank histories. An inner implementation
that uses ranks therefore needs no additional continuous clocks.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m : ℕ}

def transformRankHistory (f : Fin n → ℝ → ℝ) (H : RankHistory n) : RankHistory n :=
  fun j => (H j).map (fun z => (z.1,f j z.2))

lemma measurable_transformRankHistory {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → Fin n → ℝ → ℝ) (hf : ∀ j, Measurable (fun q : Ω × ℝ => f q.1 j q.2))
    (H : Ω → RankHistory n) (hH : Measurable H) :
    Measurable (fun q => transformRankHistory (f q) (H q)) := by
  apply measurable_pi_lambda
  intro j
  have hj := (measurable_pi_apply j).comp hH
  rw [measurable_comap_iff]
  let F : ((Ω × Unit) ⊕ (Ω × (Fin n × ℝ))) → Unit ⊕ (Fin n × ℝ) :=
    Sum.elim (fun _ => Sum.inl ()) (fun q => Sum.inr (q.2.1,f q.1 j q.2.2))
  have hF : Measurable F := measurable_const.sumElim (measurable_inr.comp
    ((measurable_fst.comp measurable_snd).prodMk
      ((hf j).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))))
  have hCode : Measurable (fun q : Ω => (q,rankObservationCode (H q j))) :=
    measurable_id.prodMk ((comap_measurable rankObservationCode).comp hj)
  have h := hF.comp ((MeasurableEquiv.prodSumDistrib Ω Unit (Fin n × ℝ)).measurable.comp hCode)
  convert h using 1
  funext q
  cases e : H q j
  · simp [F,transformRankHistory,e,rankObservationCode]
    rfl
  · simp [F,transformRankHistory,e,rankObservationCode]
    rfl

lemma clockHistoryPresent_mapValuesBy (f : Fin n → ℝ → ℝ) (H : History n) :
    clockHistoryPresent (mapHistoryValuesBy f H)=clockHistoryPresent H := by
  ext j
  cases h : H j <;> simp [clockHistoryPresent,mapHistoryValuesBy,mapObservationValues,h]

lemma clockHistoryBefore_mapValuesBy (f : Fin n → ℝ → ℝ) (H : History n) (t : ℝ) :
    clockHistoryBefore (mapHistoryValuesBy f H) t=clockHistoryBefore H t := by
  ext j
  cases h : H j with
  | none => simp [clockHistoryBefore,mapHistoryValuesBy,mapObservationValues,h]
  | some a =>
    rcases a with ⟨u,x⟩
    simp [clockHistoryBefore,mapHistoryValuesBy,mapObservationValues,h]

lemma currentRankFromClock_mapValuesBy (f : Fin n → ℝ → ℝ) (H : History n) (i : Fin n) :
    currentRankFromClock i (mapHistoryValuesBy f H)=currentRankFromClock i H := by
  unfold currentRankFromClock
  rw [clockHistoryPresent_mapValuesBy]

lemma rankHistoryFromClock_mapValuesBy (f : Fin n → ℝ → ℝ) (H : History n) (i : Fin n) :
    rankHistoryFromClock i (mapHistoryValuesBy f H)=transformRankHistory f (rankHistoryFromClock i H) := by
  funext j
  cases h : H j <;> simp [rankHistoryFromClock,transformRankHistory,mapHistoryValuesBy,mapObservationValues,h,
    clockHistoryBefore_mapValuesBy]

noncomputable def outerRankPolicy (m : ℕ) (hm : 1≤m) (L : RankLearner n (2*m)) :
    RankPolicy (OuterLearnerInput m L.rankToClock) n where
  decide p t i x H := if outerPilotAt m hm L.rankToClock p=0 then
    decide (0<outerRetainedObservation m hm L.rankToClock p i x)
    else
      let f := outerDisplayedObservation m hm L.rankToClock p
      L.policy.decide (outerInnerTraining m hm L.rankToClock p,outerInnerPolicySeed m L.rankToClock p)
        t i (f i x) (transformRankHistory f H)

lemma outerRankPolicy_measurable (m : ℕ) (hm : 1≤m) (L : RankLearner n (2*m)) :
    (outerRankPolicy m hm L).IsMeasurable := by
  let A := OuterLearnerInput m L.rankToClock
  let Ω := A × (Fin n × (Fin n × (ℝ × RankHistory n)))
  have hA : Measurable (fun q : Ω => q.1) := measurable_fst
  have ht : Measurable (fun q : Ω => q.2.1) := measurable_fst.comp measurable_snd
  have hi : Measurable (fun q : Ω => q.2.2.1) := by fun_prop
  have hx : Measurable (fun q : Ω => q.2.2.2.1) := by fun_prop
  have hH : Measurable (fun q : Ω => q.2.2.2.2) := by fun_prop
  have hd j := measurable_outerDisplayedObservation m hm L.rankToClock j
  have hr j := measurable_outerRetainedObservation m hm L.rankToClock j
  have hf : Measurable (fun q : Ω => outerDisplayedObservation m hm L.rankToClock q.1 q.2.2.1 q.2.2.2.1) := by
    have h : Measurable (fun a : (A × ℝ) × Fin n =>
        outerDisplayedObservation m hm L.rankToClock a.1.1 a.2 a.1.2) :=
      measurable_from_prod_countable_left hd
    let g : Ω → (A × ℝ) × Fin n := fun q => ((q.1,q.2.2.2.1),q.2.2.1)
    let F : (A × ℝ) × Fin n → ℝ := fun a => outerDisplayedObservation m hm L.rankToClock a.1.1 a.2 a.1.2
    have hg : Measurable g := (hA.prodMk hx).prodMk hi
    change Measurable (F ∘ g)
    exact (show Measurable F from h).comp hg
  have hPositive : Measurable (fun q : Ω => outerRetainedObservation m hm L.rankToClock q.1 q.2.2.1 q.2.2.2.1) := by
    have h : Measurable (fun a : (A × ℝ) × Fin n =>
        outerRetainedObservation m hm L.rankToClock a.1.1 a.2 a.1.2) :=
      measurable_from_prod_countable_left hr
    let g : Ω → (A × ℝ) × Fin n := fun q => ((q.1,q.2.2.2.1),q.2.2.1)
    let F : (A × ℝ) × Fin n → ℝ := fun a =>
      outerRetainedObservation m hm L.rankToClock a.1.1 a.2 a.1.2
    have hg : Measurable g := (hA.prodMk hx).prodMk hi
    change Measurable (F ∘ g)
    exact (show Measurable F from h).comp hg
  have hPast' (j : Fin n) : Measurable (fun q : Ω × ℝ =>
      outerDisplayedObservation m hm L.rankToClock q.1.1 j q.2) := by
    let F : A × ℝ → ℝ := fun a => outerDisplayedObservation m hm L.rankToClock a.1 j a.2
    let g : Ω × ℝ → A × ℝ := fun q => (q.1.1,q.2)
    have hg : Measurable g := (hA.comp measurable_fst).prodMk measurable_snd
    change Measurable (F ∘ g)
    exact (show Measurable F from hd j).comp hg
  have hPast : Measurable (fun q : Ω => transformRankHistory
      (outerDisplayedObservation m hm L.rankToClock q.1) q.2.2.2.2) :=
    measurable_transformRankHistory _ hPast' _ hH
  have hSeed : Measurable (fun q : Ω =>
      (outerInnerTraining m hm L.rankToClock q.1,outerInnerPolicySeed m L.rankToClock q.1)) :=
    ((measurable_outerInnerTraining m hm L.rankToClock).comp hA).prodMk
      ((measurable_outerInnerPolicySeed m L.rankToClock).comp hA)
  have hGuard : MeasurableSet {q : Ω | outerPilotAt m hm L.rankToClock q.1=0} :=
    measurableSet_eq_fun ((measurable_outerPilotAt m hm L.rankToClock).comp hA) measurable_const
  have hF := L.policy_isMeasurable.comp (hSeed.prodMk (ht.prodMk (hi.prodMk (hf.prodMk hPast))))
  have hP : Measurable (fun q : Ω =>
      decide (0<outerRetainedObservation m hm L.rankToClock q.1 q.2.2.1 q.2.2.2.1)) :=
    measurable_to_bool (by
      change MeasurableSet {q : Ω | decide
        (0<outerRetainedObservation m hm L.rankToClock q.1 q.2.2.1 q.2.2.2.1)=true}
      simp only [decide_eq_true_eq]
      exact measurableSet_lt measurable_const hPositive)
  exact hP.ite hGuard hF

lemma outerRankPolicy_rankToClock (m : ℕ) (hm : 1≤m) (L : RankLearner n (2*m)) :
    (outerRankPolicy m hm L).rankToClock=outerPolicy m hm L.rankToClock := by
  apply congrArg Policy.mk
  funext p t i x H
  change (outerRankPolicy m hm L).decide p (currentRankFromClock i H) i x (rankHistoryFromClock i H) =
    (outerPolicy m hm L.rankToClock).decide p t i x H
  simp only [outerRankPolicy,outerPolicy]
  split_ifs with h
  · simp only [outerPositivePolicy,Policy.pullbackValuesBy,firstPositiveRule]
    split_ifs with hp <;> simp [hp]
  · simp only [outerBoundedPolicy,Policy.pullbackValuesBy,RankLearner.rankToClock_policy,
      RankPolicy.rankToClock,currentRankFromClock_mapValuesBy,rankHistoryFromClock_mapValuesBy]
    rfl

noncomputable def outerFairRankLearner (hm : 1≤m) (L : RankLearner n (2*m)) (b : ℕ) :
    RankLearner n (outerSampleBudget m) :=
  let B := outerFairMarkLearner hm L.rankToClock b
  let f := fun p : B.Seed × Transcript n =>
    (decodedReservoir p.2,outerSeedFromMarks L.rankToClock (unpackOuterMarks (fairMarkDecoder b p.1.1)) p.1.2)
  have hf : Measurable f := by
    let S := B.Seed × Transcript n
    have hB : Measurable (fun p : S => p.1.1) := measurable_fst.comp measurable_fst
    have hL : Measurable (fun p : S => p.1.2) := measurable_snd.comp measurable_fst
    have hd : Measurable (fairMarkDecoder (n := n) (m := m) b) := measurable_of_countable _
    have hu := (measurePreserving_unpackOuterMarks n m).measurable.comp (hd.comp hB)
    exact (measurable_decodedReservoir.comp measurable_snd).prodMk
      ((outerSeedFromMarks_measurePreserving L.rankToClock).measurable.comp (hu.prodMk hL))
  let A := OuterLearnerInput m L.rankToClock
  let O := Fin n × (Fin n × (ℝ × RankHistory n))
  let g : (B.Seed × Transcript n) × O → A × O := fun q => (f q.1,q.2)
  let u : A × O → Bool := fun q => (outerRankPolicy m hm L).decide
    q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
  have hg : Measurable g := (hf.comp measurable_fst).prodMk measurable_snd
  have hu : Measurable u := outerRankPolicy_measurable m hm L
  have hDec : Measurable (u ∘ g) := hu.comp hg
  { Seed := B.Seed
    seedLaw := B.seedLaw
    request := firstAvailableRequest (outerSampleBudget m)
    measurable_request := measurable_firstAvailableRequest
    decide := fun r T t i x H => (outerRankPolicy m hm L).decide (f (r,T)) t i x H
    measurable_decide := hDec }

theorem outerFairRankLearner_expectedReward (hm : 1≤m) (L : RankLearner n (2*m))
    (b : ℕ) (P : Instance n) :
    (outerFairRankLearner hm L b).expectedReward P =
      (outerFairMarkLearner hm L.rankToClock b).expectedReward P := by
  let B := outerFairMarkLearner hm L.rankToClock b
  let R := outerFairRankLearner hm L b
  rw [← R.rankToClock_expectedReward P]
  have hEq : R.rankToClock.policy=B.policy := by
    apply congrArg Policy.mk
    funext p t i x H
    obtain ⟨y,u,s⟩ := p
    let a := (y,outerSeedFromMarks L.rankToClock (unpackOuterMarks (fairMarkDecoder b u)) s)
    have h := congrArg (fun π : Policy (OuterLearnerInput m L.rankToClock) n => π.decide a t i x H)
      (outerRankPolicy_rankToClock m hm L)
    change (outerRankPolicy m hm L).rankToClock.decide
      (decodedReservoir (trainingTranscript (firstAvailableRequest _) (u,s) y),a.2) t i x H = _
    rw [decodedReservoir_firstAvailable_transcript]
    let ν := Measure.pi (fun _ : Fin (n*(outerSampleBudget m+1)) => Probability.fairBitVectorLaw b)
    letI : IsProbabilityMeasure ν := by
      dsimp only [ν]
      infer_instance
    exact h.trans (outerMarkedLearner_decide ν hm L.rankToClock (fairMarkDecoder b)
      (measurable_of_countable _) y u s t i x H).symm
  change (∫ ω : (B.randomizedPolicy P).World,
      R.rankToClock.policy.reward ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (B.randomizedPolicy P).seedLaw) =
    ∫ ω : (B.randomizedPolicy P).World,
      B.policy.reward ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (B.randomizedPolicy P).seedLaw
  rw [hEq]
  rfl

end ProphetSecretary.Statistics.Calibration
