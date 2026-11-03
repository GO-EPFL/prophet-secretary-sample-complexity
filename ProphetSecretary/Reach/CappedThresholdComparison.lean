import ProphetSecretary.Model.CappedThresholdFamily
import ProphetSecretary.Model.PositiveArrivalBands
import ProphetSecretary.Reach.MarkovStrict
import ProphetSecretary.Model.UniformPolicyMixture
import ProphetSecretary.Model.PolicySeedTransport

/-!
# Coupling numerical and exact capped threshold rules

On accurate threshold evaluations, a different action requires a positive
candidate in the exact continuation band. The action comparison can use
all potential arrivals analytically; a running policy uses only its past.
The numerical rule needs no deletion monotonicity.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

noncomputable def canonicalCappedThreshold (Q : Instance n) (z : ℝ) :
    Seed → ℝ → Fin n → History n → ℝ :=
  fun _ t i H => Q.valueThreshold 1 z (unseen H) t i

noncomputable def canonicalCappedPolicy (Q : Instance n) (z : ℝ) : Policy Seed n :=
  cappedHistoryThresholdPolicy (canonicalCappedThreshold Q z)

lemma canonicalCappedThreshold_at_arrival (Q : Instance n) (z : ℝ) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) :
    canonicalCappedThreshold Q z r (u i) i (history Finset.univ x u (u i)) =
      Q.continuationAtArrival 1 z x u i := by
  simpa only [canonicalCappedThreshold, one_mul] using
    (Q.continuationAtArrival_eq_threshold (by norm_num : (0 : ℝ) < 1) z x u i).symm

lemma cappedDecision_disagreement {a b x h : ℝ} (hacc : |a-b| ≤ h)
    (hdiff : decide (x = 1 ∨ (0 < x ∧ a ≤ x)) ≠ decide (x = 1 ∨ (0 < x ∧ b ≤ x))) :
    0 < x ∧ |x-b| ≤ h := by
  by_cases hcap : x = 1
  · simp [hcap] at hdiff
  by_cases hx : 0 < x
  · refine ⟨hx, ?_⟩
    have hab := abs_le.mp hacc
    by_cases ha : a ≤ x <;> by_cases hb : b ≤ x <;> simp [hcap, hx, ha, hb] at hdiff
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simp [hcap, hx] at hdiff

/-- Difference of potential actions on a common complete trajectory. -/
def Policy.actionDisagreement (π σ : Policy Seed n) (r : Seed) (x u : Fin n → ℝ) : Prop :=
  ∃ i, π.action r Finset.univ x u i ≠ σ.action r Finset.univ x u i

noncomputable def cappedThresholdError (Q : Instance n) (z : ℝ)
    (θ : Seed → ℝ → Fin n → History n → ℝ) (r : Seed) (x u : Fin n → ℝ) (i : Fin n) : ℝ :=
  |θ r (u i) i (history Finset.univ x u (u i)) - Q.continuationAtArrival 1 z x u i|

/-- The probability of a different action is bounded by the actual numerical
error event plus the positive-count boundary width. -/
theorem cappedThreshold_actionDisagreement_probability [MeasurableSpace Seed]
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (θ : Seed → ℝ → Fin n → History n → ℝ)
    {z h : ℝ} (hz : 0 < z) (hh : 0 ≤ h) :
    (P.worldLaw ν).real {ω : World n Seed |
      (cappedHistoryThresholdPolicy θ).actionDisagreement (canonicalCappedPolicy Q z)
        ω.2.2 ω.1 ω.2.1} ≤
      (P.worldLaw ν).real {ω : World n Seed | ∃ i, h < cappedThresholdError Q z θ ω.2.2 ω.1 ω.2.1 i} +
        (2*h/(z/(1+Q.positiveCount)))*P.positiveCount := by
  let μ := P.worldLaw ν
  let E : Set (World n Seed) := {ω | ∃ i, h < cappedThresholdError Q z θ ω.2.2 ω.1 ω.2.1 i}
  let B : Fin n → Set (World n Seed) := fun i => {ω | 0 < ω.1 i ∧
    |ω.1 i - Q.continuationAtArrival 1 z ω.1 ω.2.1 i| ≤ h}
  have hsub : {ω : World n Seed |
      (cappedHistoryThresholdPolicy θ).actionDisagreement (canonicalCappedPolicy Q z)
        ω.2.2 ω.1 ω.2.1} ⊆ E ∪ ⋃ i, B i := by
    intro ω hw
    by_cases he : ω ∈ E
    · exact Or.inl he
    · right
      obtain ⟨i, hi⟩ := hw
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      have hacc : cappedThresholdError Q z θ ω.2.2 ω.1 ω.2.1 i ≤ h :=
        le_of_not_gt (fun hbad => he ⟨i, hbad⟩)
      simp only [canonicalCappedPolicy, Policy.action, cappedHistoryThresholdPolicy] at hi
      rw [canonicalCappedThreshold_at_arrival] at hi
      exact cappedDecision_disagreement hacc hi
  have hb (i : Fin n) : μ.real (B i) ≤
      (2*h/(z/(1+Q.positiveCount)))*(P.law i).real (Ioi 0) := by
    simpa only [μ, B, one_mul] using
      Q.positiveAcceptanceBandUnder_probability P hQ ν (by norm_num : (0 : ℝ) < 1) hz hh i
  calc
    _ ≤ μ.real (E ∪ ⋃ i, B i) := measureReal_mono hsub
    _ ≤ μ.real E + μ.real (⋃ i, B i) := measureReal_union_le _ _
    _ ≤ μ.real E + ∑ i, μ.real (B i) :=
      add_le_add le_rfl (measureReal_iUnion_fintype_le B)
    _ ≤ μ.real E + ∑ i, (2*h/(z/(1+Q.positiveCount)))*(P.law i).real (Ioi 0) :=
      add_le_add le_rfl (Finset.sum_le_sum fun i _ => hb i)
    _ = _ := by rw [← Finset.mul_sum]; rfl

lemma Policy.stoppingTime_eq_of_actions_eq (π σ : Policy Seed n)
    (r : Seed) (x u : Fin n → ℝ)
    (h : ∀ i, π.action r Finset.univ x u i = σ.action r Finset.univ x u i) :
    π.stoppingTime r Finset.univ x u = σ.stoppingTime r Finset.univ x u := by
  have ha : π.accepted r Finset.univ x u = σ.accepted r Finset.univ x u := by
    ext i
    simp only [Policy.mem_accepted, h i]
  exact congrArg (fun A : Finset (Fin n) =>
    (insert 1 (A.image u)).min' ⟨1, Finset.mem_insert_self _ _⟩) ha

lemma canonicalCappedPolicy_isMeasurable [MeasurableSpace Seed]
    (Q : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw) {z : ℝ} (hz : 0 ≤ z) :
    (canonicalCappedPolicy Q z : Policy Seed n).IsMeasurable := by
  let Ω := Seed × (ℝ × (Fin n × (ℝ × History n)))
  have hH : Measurable (fun x : Ω => unseen x.2.2.2.2) :=
    measurable_unseen.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hi : Measurable (fun x : Ω => x.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have ht : Measurable (fun x : Ω => x.2.1) := measurable_fst.comp measurable_snd
  have hx : Measurable (fun x : Ω => x.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hm0 : Measurable (fun a : Finset (Fin n) × (Fin n × ℝ) =>
      Q.valueThreshold 1 z a.1 a.2.2 a.2.1) :=
    Q.valueThreshold_jointMeasurable hQ (w := (1 : ℝ)) (c := z) zero_le_one hz
  have hmap : Measurable (fun x : Ω => (unseen x.2.2.2.2, (x.2.2.1,x.2.1))) :=
    hH.prodMk (hi.prodMk ht)
  have hcomp := hm0.comp hmap
  have hm : Measurable (fun x : Ω => Q.valueThreshold 1 z (unseen x.2.2.2.2) x.2.1 x.2.2.1) := by
    simpa only [Function.comp_def] using hcomp
  have hc : MeasurableSet {x : Ω | x.2.2.2.1 = 1} := measurableSet_eq_fun hx measurable_const
  have hp : MeasurableSet {x : Ω | 0 < x.2.2.2.1} := measurableSet_lt measurable_const hx
  have hb : MeasurableSet {x : Ω | Q.valueThreshold 1 z (unseen x.2.2.2.2) x.2.1 x.2.2.1 ≤ x.2.2.2.1} :=
    measurableSet_le hm hx
  change Measurable (fun x : Ω => (canonicalCappedPolicy Q z).decide x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
  apply measurable_to_bool
  change MeasurableSet {x : Ω | (canonicalCappedPolicy Q z).decide
    x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 = true}
  simp only [canonicalCappedPolicy, canonicalCappedThreshold, cappedHistoryThresholdPolicy, decide_eq_true_eq]
  have he : {x : Ω | x.2.2.2.1 = 1 ∨ 0 < x.2.2.2.1 ∧
      Q.valueThreshold 1 z (unseen x.2.2.2.2) x.2.1 x.2.2.1 ≤ x.2.2.2.1} =
    {x : Ω | x.2.2.2.1 = 1} ∪ ({x : Ω | 0 < x.2.2.2.1} ∩
      {x : Ω | Q.valueThreshold 1 z (unseen x.2.2.2.2) x.2.1 x.2.2.1 ≤ x.2.2.2.1}) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
  rw [he]
  exact hc.union (hp.inter hb)

lemma canonicalCappedPolicy_meanDuration_le_reach [MeasurableSpace Seed]
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {z : ℝ} (hz : 0 ≤ z) (i : Fin n) :
    (canonicalCappedPolicy Q z : Policy Seed n).meanDuration P ν ≤
      (canonicalCappedPolicy Q z : Policy Seed n).reachProbability P ν i := by
  let a : Seed → Finset (Fin n) → ℝ → Fin n → ℝ → Bool := fun _ A t j x =>
    decide (x=1 ∨ (0<x ∧ Q.valueThreshold 1 z A t j ≤ x))
  have hmono : DeletionMonotoneAcceptance a := by
    intro _ t _ j x _ A B hj hAB haccept
    have hv := Q.valueThreshold_monotone hQ (by norm_num : (0 : ℝ) < 1) hz () t j A B hj hAB
    simp only [a, decide_eq_true_eq] at haccept ⊢
    exact haccept.imp_right (fun hx => ⟨hx.1, hv.trans hx.2⟩)
  exact markovPolicy.meanDuration_le_reachProbability a hmono
    (canonicalCappedPolicy_isMeasurable Q hQ hz) P ν i

lemma Policy.measurableSet_actionDisagreement [MeasurableSpace Seed] (π σ : Policy Seed n)
    (hπ : π.IsMeasurable) (hσ : σ.IsMeasurable) :
    MeasurableSet {ω : World n Seed | π.actionDisagreement σ ω.2.2 ω.1 ω.2.1} := by
  have he : {ω : World n Seed | π.actionDisagreement σ ω.2.2 ω.1 ω.2.1} =
      ⋃ i : Fin n, {ω : World n Seed | π.action ω.2.2 Finset.univ ω.1 ω.2.1 i ≠
        σ.action ω.2.2 Finset.univ ω.1 ω.2.1 i} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Policy.actionDisagreement]
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  have hr : Measurable (fun ω : World n Seed => ω.2.2) := by fun_prop
  have hx (j : Fin n) : Measurable (fun ω : World n Seed => ω.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have hu (j : Fin n) : Measurable (fun ω : World n Seed => ω.2.1 j) :=
    (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  exact (measurableSet_eq_fun (π.measurable_action hπ hr hx hu Finset.univ i)
    (σ.measurable_action hσ hr hx hu Finset.univ i)).compl

lemma Policy.stoppingTime_eq_of_not_disagreement (π σ : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (h : ¬π.actionDisagreement σ r x u) :
    π.stoppingTime r Finset.univ x u = σ.stoppingTime r Finset.univ x u := by
  apply π.stoppingTime_eq_of_actions_eq σ r x u
  intro i
  by_contra hi
  exact h ⟨i, hi⟩

lemma Policy.meanDuration_sub_le_disagreement [MeasurableSpace Seed]
    (π σ : Policy Seed n) (hπ : π.IsMeasurable) (hσ : σ.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    π.meanDuration P ν - σ.meanDuration P ν ≤
      (P.worldLaw ν).real {ω : World n Seed | π.actionDisagreement σ ω.2.2 ω.1 ω.2.1} := by
  let E : Set (World n Seed) := {ω | π.actionDisagreement σ ω.2.2 ω.1 ω.2.1}
  have hE : MeasurableSet E := π.measurableSet_actionDisagreement σ hπ hσ
  unfold Policy.meanDuration
  rw [← integral_sub (P.integrable_worldTime ν π hπ Finset.univ)
    (P.integrable_worldTime ν σ hσ Finset.univ)]
  have hI := (integrable_const (1 : ℝ) : Integrable (fun _ : World n Seed => (1 : ℝ)) (P.worldLaw ν)).indicator hE
  have hm := integral_mono_ae ((P.integrable_worldTime ν π hπ Finset.univ).sub
    (P.integrable_worldTime ν σ hσ Finset.univ)) hI (by
      filter_upwards [P.worldTime_mem_unitInterval ν π Finset.univ,
        P.worldTime_mem_unitInterval ν σ Finset.univ] with ω hTπ hTσ
      change π.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 -
        σ.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 ≤ E.indicator (fun _ => (1 : ℝ)) ω
      by_cases he : ω ∈ E
      · rw [Set.indicator_of_mem he]
        linarith [hTπ.2, hTσ.1]
      · rw [Set.indicator_of_notMem he,
          π.stoppingTime_eq_of_not_disagreement σ ω.2.2 ω.1 ω.2.1 he]
        simp)
  rw [integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one] at hm
  exact hm

lemma Policy.reachProbability_reverse_le_disagreement [MeasurableSpace Seed]
    (π σ : Policy Seed n) (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    σ.reachProbability P ν i ≤ π.reachProbability P ν i +
      (P.worldLaw ν).real {ω : World n Seed | π.actionDisagreement σ ω.2.2 ω.1 ω.2.1} := by
  let E : Set (World n Seed) := {ω | π.actionDisagreement σ ω.2.2 ω.1 ω.2.1}
  let R (ρ : Policy Seed n) : Set (World n Seed) := fun ω => ρ.Reaches ω.2.2 ω.1 ω.2.1 i
  have hs : R σ ⊆ R π ∪ E := by
    intro ω hω
    by_cases he : ω ∈ E
    · exact Or.inr he
    · left
      change ω.2.1 i ≤ π.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
      rw [π.stoppingTime_eq_of_not_disagreement σ ω.2.2 ω.1 ω.2.1 he]
      exact hω
  exact (measureReal_mono hs).trans (measureReal_union_le _ _)

/-- Numerical reach transfer, expressed using the actual threshold-error event.
The deletion comparison is applied only to the exact reference rule. -/
theorem cappedThreshold_duration_le_reach_add_error [MeasurableSpace Seed]
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (θ : Seed → ℝ → Fin n → History n → ℝ)
    (hθ : (cappedHistoryThresholdPolicy θ).IsMeasurable) {z h : ℝ}
    (hz : 0 < z) (hh : 0 ≤ h) (i : Fin n) :
    (cappedHistoryThresholdPolicy θ).meanDuration P ν ≤
      (cappedHistoryThresholdPolicy θ).reachProbability P ν i + 2 *
        ((P.worldLaw ν).real {ω : World n Seed | ∃ j, h < cappedThresholdError Q z θ ω.2.2 ω.1 ω.2.1 j} +
          (2*h/(z/(1+Q.positiveCount)))*P.positiveCount) := by
  have hd := cappedThreshold_actionDisagreement_probability Q P hQ ν θ hz hh
  have hT := (cappedHistoryThresholdPolicy θ).meanDuration_sub_le_disagreement
    (canonicalCappedPolicy Q z) hθ (canonicalCappedPolicy_isMeasurable Q hQ hz.le) P ν
  have hq := (cappedHistoryThresholdPolicy θ).reachProbability_reverse_le_disagreement
    (canonicalCappedPolicy Q z) P ν i
  have hTq := canonicalCappedPolicy_meanDuration_le_reach Q P hQ ν hz.le i
  linarith only [hd, hT, hq, hTq]

lemma Policy.reward_eq_of_actions_eq (π σ : Policy Seed n) (r : Seed) (x u : Fin n → ℝ)
    (h : ∀ i, π.action r Finset.univ x u i = σ.action r Finset.univ x u i) :
    π.reward r Finset.univ x u = σ.reward r Finset.univ x u := by
  have ha : π.accepted r Finset.univ x u = σ.accepted r Finset.univ x u := by
    ext i
    simp only [Policy.mem_accepted, h i]
  have ht := π.stoppingTime_eq_of_actions_eq σ r x u h
  unfold Policy.reward
  apply Finset.sum_congr rfl
  intro i _
  have he : π.ActualSelects r Finset.univ x u i ↔ σ.ActualSelects r Finset.univ x u i := by
    simp only [Policy.ActualSelects, Policy.Selects, ha, ht]
  by_cases hs : σ.ActualSelects r Finset.univ x u i
  · rw [if_pos (he.mpr hs), if_pos hs]
  · rw [if_neg (fun hp => hs (he.mp hp)), if_neg hs]

lemma RandomizedPolicy.pullbackSeed_expectedDuration (π : RandomizedPolicy n)
    {S : Type} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (f : S → π.Seed) (hf : Measurable f) (hLaw : MeasurePreserving f ν π.seedLaw) (P : Instance n) :
    (π.pullbackSeed ν f hf).expectedDuration P = π.expectedDuration P := by
  have hWorld : MeasurePreserving (Prod.map id (Prod.map id f)) (P.worldLaw ν) (P.worldLaw π.seedLaw) :=
    (MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Instance.clocksLaw n)).prod hLaw)
  exact hWorld.hasLaw.integral_comp π.measurable_realizedDuration.aestronglyMeasurable

lemma RandomizedPolicy.ofRule_scalarObjective_eq_of_actions_eq_ae {S : Type} [MeasurableSpace S]
    (P : Instance n) (ν : Measure S) [IsProbabilityMeasure ν] (π σ : Policy S n)
    (hπ : π.IsMeasurable) (hσ : σ.IsMeasurable)
    (ha : ∀ᵐ ω : ProphetSecretary.Model.World n S ∂P.worldLaw ν, ∀ i,
      π.action ω.2.2 Finset.univ ω.1 ω.2.1 i = σ.action ω.2.2 Finset.univ ω.1 ω.2.1 i)
    (w c : ℝ) :
    (RandomizedPolicy.ofRule ν π hπ).scalarObjective P w c =
      (RandomizedPolicy.ofRule ν σ hσ).scalarObjective P w c := by
  unfold RandomizedPolicy.scalarObjective
  apply integral_congr_ae
  filter_upwards [ha] with ω h
  change w*π.reward ω.2.2 Finset.univ ω.1 ω.2.1 + c*π.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 =
    w*σ.reward ω.2.2 Finset.univ ω.1 ω.2.1 + c*σ.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
  rw [π.reward_eq_of_actions_eq σ ω.2.2 ω.1 ω.2.1 h,
    π.stoppingTime_eq_of_actions_eq σ ω.2.2 ω.1 ω.2.1 h]

/-- Disagreement costs at most `1+z` in the bounded scalar objective. -/
lemma RandomizedPolicy.ofRule_scalarObjective_sub_le_disagreement {S : Type} [MeasurableSpace S]
    (P : Instance n) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    (ν : Measure S) [IsProbabilityMeasure ν] (π σ : Policy S n)
    (hπ : π.IsMeasurable) (hσ : σ.IsMeasurable) {z : ℝ} (hz : 0 ≤ z) :
    (RandomizedPolicy.ofRule ν σ hσ).scalarObjective P 1 z -
      (RandomizedPolicy.ofRule ν π hπ).scalarObjective P 1 z ≤
      (1+z)*(P.worldLaw ν).real {ω : ProphetSecretary.Model.World n S | π.actionDisagreement σ ω.2.2 ω.1 ω.2.1} := by
  let μ := P.worldLaw ν
  let E : Set (ProphetSecretary.Model.World n S) := {ω | π.actionDisagreement σ ω.2.2 ω.1 ω.2.1}
  let f (ρ : Policy S n) (ω : ProphetSecretary.Model.World n S) :=
    ρ.reward ω.2.2 Finset.univ ω.1 ω.2.1 + z*ρ.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
  have hE : MeasurableSet E := π.measurableSet_actionDisagreement σ hπ hσ
  have hP := P.integrable_maximum_of_bounded hcap
  have hf (ρ : Policy S n) (hρ : ρ.IsMeasurable) : Integrable (f ρ) μ :=
    ((RandomizedPolicy.ofRule ν ρ hρ).integrable_realizedReward P hP).add
      ((P.integrable_worldTime ν ρ hρ Finset.univ).const_mul z)
  have hv : MeasurePreserving (fun ω : ProphetSecretary.Model.World n S => ω.1) μ P.valuesLaw := measurePreserving_fst
  have hvc : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ 1 := ae_all_iff.mpr (fun i =>
    (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hcap i))
  have hI := (integrable_const (1+z) : Integrable (fun _ : ProphetSecretary.Model.World n S => 1+z) μ).indicator hE
  have hm := integral_mono_ae ((hf σ hσ).sub (hf π hπ)) hI (by
    filter_upwards [hv.quasiMeasurePreserving.ae P.ae_nonnegative, hv.quasiMeasurePreserving.ae hvc,
      P.worldTime_mem_unitInterval ν π Finset.univ, P.worldTime_mem_unitInterval ν σ Finset.univ]
      with ω hx0 hx1 htπ htσ
    change f σ ω - f π ω ≤ E.indicator (fun _ => 1+z) ω
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he]
      have hrσ := (σ.reward_le_maximum ω.2.2 Finset.univ ω.1 ω.2.1).trans
        (Instance.maximum_le ω.1 zero_le_one hx1)
      have hrπ := π.reward_nonnegative ω.2.2 Finset.univ ω.1 ω.2.1 hx0
      dsimp [f]
      linarith [mul_le_mul_of_nonneg_left htσ.2 hz, mul_nonneg hz htπ.1]
    · rw [Set.indicator_of_notMem he]
      have ha (i : Fin n) : π.action ω.2.2 Finset.univ ω.1 ω.2.1 i =
          σ.action ω.2.2 Finset.univ ω.1 ω.2.1 i := by
        by_contra hi
        exact he ⟨i,hi⟩
      dsimp [f]
      rw [π.reward_eq_of_actions_eq σ ω.2.2 ω.1 ω.2.1 ha,
        π.stoppingTime_eq_of_actions_eq σ ω.2.2 ω.1 ω.2.1 ha]
      simp)
  simp only [Pi.sub_apply] at hm
  rw [integral_sub (hf σ hσ) (hf π hπ), integral_indicator_const (1+z) hE,
    smul_eq_mul, mul_comm (μ.real E)] at hm
  simp only [RandomizedPolicy.scalarObjective, RandomizedPolicy.ofRule, RandomizedPolicy.realizedReward,
    RandomizedPolicy.realizedDuration, one_mul]
  change (∫ ω, f σ ω ∂μ) - (∫ ω, f π ω ∂μ) ≤ (1+z)*μ.real E
  exact hm

end ProphetSecretary.Model
