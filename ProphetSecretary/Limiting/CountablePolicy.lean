import ProphetSecretary.Limiting.CountableCandidates
import ProphetSecretary.Limiting.CountableFirstAcceptance

/-!
# General randomized policies on the countable configuration

The callbacks see only the seed, the current offer, and the actual past. A
measurable first accepted point must exist whenever there is an acceptance;
this is an admissibility requirement, not an assumed optimizer theorem. In
particular no finite-support or Markov restriction is imposed here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

variable {Seed : Type*}

def CountableRule.IsMeasurable [MeasurableSpace Seed] (π : CountableRule Seed) : Prop :=
  Measurable (fun z : Seed × (ℝ × (ℕ × (ℝ × (IndividualHistory × Measure Point)))) =>
    π.individual z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2) ∧
  Measurable (fun z : Seed × (Point × (IndividualHistory × Measure Point)) =>
    π.poisson z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2)

noncomputable def CountableRule.candidateAction (π : CountableRule Seed) (v : CompleteWorld Seed)
    (i : Candidate) : Bool :=
  let p := candidatePoint v i
  let h := individualHistory v.2.1 v.2.2.1 p.1
  let ξ := anonymousHistory v.1 p.1
  match i with
  | Sum.inl j => π.individual v.2.2.2 p.1 j p.2 h ξ
  | Sum.inr _ => π.poisson v.2.2.2 p.1 p.2 h ξ

noncomputable def codeTime (v : CompleteWorld Seed) (i : ℕ) : ℝ := (codePoint v i).1
noncomputable def codeValue (v : CompleteWorld Seed) (i : ℕ) : ℝ := (codePoint v i).2

noncomputable def CountableRule.codeAccepted (π : CountableRule Seed) (v : CompleteWorld Seed) (i : ℕ) : Prop :=
  codePresent v i ∧ codeTime v i ∈ Icc (0 : ℝ) 1 ∧
    π.candidateAction v (candidateEnumeration.symm i) = true

noncomputable def CountableRule.realizedReward (π : CountableRule Seed) (a : ℝ) : CompleteWorld Seed → ℝ :=
  FirstAcceptance.reward a π.codeAccepted codeTime codeValue

noncomputable def CountableRule.realizedDuration (π : CountableRule Seed) : CompleteWorld Seed → ℝ :=
  FirstAcceptance.stoppingTime π.codeAccepted codeTime

variable [MeasurableSpace Seed]

lemma CountableRule.measurable_candidateAction (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (i : Candidate) : Measurable (fun v => π.candidateAction v i) := by
  have hr : Measurable (fun v : CompleteWorld Seed => v.2.2.2) := by fun_prop
  have ht : Measurable (fun v : CompleteWorld Seed => (candidatePoint v i).1) :=
    measurable_fst.comp (measurable_candidatePoint i)
  have hx : Measurable (fun v : CompleteWorld Seed => (candidatePoint v i).2) :=
    measurable_snd.comp (measurable_candidatePoint i)
  have hH : Measurable (fun v : CompleteWorld Seed =>
      individualHistory v.2.1 v.2.2.1 (candidatePoint v i).1) :=
    measurable_individualHistory (fun j => (measurable_pi_apply j).comp (by fun_prop))
      (fun j => (measurable_pi_apply j).comp (by fun_prop)) ht
  have hξ : Measurable (fun v : CompleteWorld Seed => anonymousHistory v.1 (candidatePoint v i).1) :=
    measurable_anonymousHistory measurable_fst ht
  cases i with
  | inl j => exact hπ.1.comp (hr.prodMk (ht.prodMk (measurable_const.prodMk (hx.prodMk (hH.prodMk hξ)))))
  | inr kj => exact hπ.2.comp (hr.prodMk ((ht.prodMk hx).prodMk (hH.prodMk hξ)))

lemma measurable_codeTime (i : ℕ) : Measurable (fun v : CompleteWorld Seed => codeTime v i) :=
  measurable_fst.comp (measurable_codePoint i)

lemma measurable_codeValue (i : ℕ) : Measurable (fun v : CompleteWorld Seed => codeValue v i) :=
  measurable_snd.comp (measurable_codePoint i)

lemma CountableRule.measurableSet_codeAccepted (π : CountableRule Seed) (hπ : π.IsMeasurable) (i : ℕ) :
    MeasurableSet {v | π.codeAccepted v i} :=
  (measurableSet_codePresent i).inter (((measurable_codeTime i) measurableSet_Icc).inter
    ((π.measurable_candidateAction hπ _ ) (measurableSet_singleton true)))

lemma CountableRule.measurable_realizedReward (π : CountableRule Seed) (hπ : π.IsMeasurable) (a : ℝ) :
    Measurable (π.realizedReward a) :=
  FirstAcceptance.measurable_reward a (π.measurableSet_codeAccepted hπ) measurable_codeTime measurable_codeValue

lemma CountableRule.measurable_realizedDuration (π : CountableRule Seed) (hπ : π.IsMeasurable) :
    Measurable π.realizedDuration :=
  FirstAcceptance.measurable_stoppingTime (π.measurableSet_codeAccepted hπ) measurable_codeTime

/-- The complete accepted set may be infinite, but its minimum time must be
attained almost surely. No continuation or optimizer property is assumed. -/
def CountableRule.Admissible (π : CountableRule Seed) (B : CountableInstance) (ν : Measure Seed) : Prop :=
  ∀ᵐ v ∂B.completeWorldLaw ν, FirstAcceptance.HasFirstIfAccepted π.codeAccepted codeTime v

omit [MeasurableSpace Seed] in
lemma CountableRule.duration_bounds (π : CountableRule Seed) (v : CompleteWorld Seed) :
    π.realizedDuration v ∈ Icc (0 : ℝ) 1 := by
  have hupper := FirstAcceptance.stoppingTime_le_one (A := π.codeAccepted) (u := codeTime)
    (ω := v) (fun i hi => hi.2.1.2)
  by_cases he : ∃ i, FirstAcceptance.Earliest π.codeAccepted codeTime v i
  · obtain ⟨i,hi⟩ := he
    exact ⟨by rw [CountableRule.realizedDuration,FirstAcceptance.stoppingTime_of_earliest hi]; exact hi.1.2.1.1,hupper⟩
  · rw [CountableRule.realizedDuration,FirstAcceptance.stoppingTime_of_no_first he]
    exact ⟨zero_le_one,le_rfl⟩

omit [MeasurableSpace Seed] in
lemma CountableRule.no_first_reward (π : CountableRule Seed) (a : ℝ) (v : CompleteWorld Seed)
    (h : ¬∃ i, FirstAcceptance.Earliest π.codeAccepted codeTime v i) : π.realizedReward a v = a := by
  rw [CountableRule.realizedReward,FirstAcceptance.reward,
    (FirstAcceptance.selectedCode_eq_zero_iff _ _ _).mpr h,if_pos rfl]

lemma CountableRule.reach_iff (π : CountableRule Seed) (B : CountableInstance) (ν : Measure Seed)
    (hπ : π.Admissible B ν) :
    ∀ᵐ v ∂B.completeWorldLaw ν, ∀ t : ℝ,
      t ≤ π.realizedDuration v ↔ t ≤ 1 ∧ ∀ i, π.codeAccepted v i → t ≤ codeTime v i := by
  filter_upwards [hπ] with v hv
  intro t
  exact FirstAcceptance.le_stoppingTime_iff hv (fun i hi => hi.2.1.2) t

end ProphetSecretary.Limiting.CountableInstance
