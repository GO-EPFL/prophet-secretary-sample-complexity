import ProphetSecretary.Limiting.CountableSingleIndividualTransport
import ProphetSecretary.Model.Truncation

/-!
# Causal reconstruction of one observed value using an independent seed

The reconstruction map is applied to the current value of one identity and
to its already observed history entry. Presence, clocks and zero observations
are retained. The map never accesses an unseen value.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

variable {Seed : Type*}

noncomputable def CountableRule.pullbackSeededIndividual (π : CountableRule Seed) (i : ℕ)
    (g : Seed → ℝ → ℝ) : CountableRule Seed where
  individual r t j x H ξ := π.individual r t j (if j=i then g r x else x)
    (mapSingleIndividualHistory i (g r) H) ξ
  poisson r t x H ξ := π.poisson r t x (mapSingleIndividualHistory i (g r) H) ξ

lemma measurable_seededSingleIndividualHistory [MeasurableSpace Seed] (i : ℕ)
    {g : Seed → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : Seed × IndividualHistory => mapSingleIndividualHistory i (g z.1) z.2) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j=i
  · simpa only [mapSingleIndividualHistory,if_pos hj] using
      Model.measurable_mapObservationValuesBy hg measurable_fst ((measurable_pi_apply j).comp measurable_snd)
  · simpa only [mapSingleIndividualHistory,if_neg hj,Function.comp_def] using
      (measurable_pi_apply j).comp (measurable_snd : Measurable (fun z : Seed × IndividualHistory => z.2))

lemma CountableRule.pullbackSeededIndividual_isMeasurable [MeasurableSpace Seed]
    (π : CountableRule Seed) (hπ : π.IsMeasurable) (i : ℕ)
    {g : Seed → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) :
    (π.pullbackSeededIndividual i g).IsMeasurable := by
  have hH := measurable_seededSingleIndividualHistory i hg
  have hCurrent : Measurable (fun z : Seed × (ℝ × (ℕ × (ℝ × (IndividualHistory × Measure Point)))) =>
      if z.2.2.1=i then g z.1 z.2.2.2.1 else z.2.2.2.1) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd.snd.fst measurable_const)
      (hg.comp (measurable_fst.prodMk measurable_snd.snd.snd.fst)) measurable_snd.snd.snd.fst
  refine ⟨?_,?_⟩
  · exact hπ.1.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
      (measurable_snd.snd.fst.prodMk (hCurrent.prodMk
        ((hH.comp (measurable_fst.prodMk measurable_snd.snd.snd.snd.fst)).prodMk measurable_snd.snd.snd.snd.snd)))))
  · exact hπ.2.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
      ((hH.comp (measurable_fst.prodMk measurable_snd.snd.fst)).prodMk measurable_snd.snd.snd)))

lemma CountableRule.pullbackSeededIndividual_candidateAction (π : CountableRule Seed) (i : ℕ)
    (g : Seed → ℝ → ℝ) (v : CompleteWorld Seed) (k : Candidate) :
    (π.pullbackSeededIndividual i g).candidateAction v k=
      π.candidateAction (mapSingleIndividualWorld i (g v.2.2.2) v) k := by
  have h : (π.pullbackSeededIndividual i g).candidateAction v k=
      (π.pullbackSingleIndividual i (g v.2.2.2)).candidateAction v k := by
    cases k <;> rfl
  exact h.trans (π.pullbackSingleIndividual_candidateAction i (g v.2.2.2) v k)

lemma CountableRule.pullbackSeededIndividual_codeAccepted (π : CountableRule Seed) (i : ℕ)
    (g : Seed → ℝ → ℝ) (v : CompleteWorld Seed) (k : ℕ) :
    (π.pullbackSeededIndividual i g).codeAccepted v k ↔
      π.codeAccepted (mapSingleIndividualWorld i (g v.2.2.2) v) k := by
  simp only [CountableRule.codeAccepted,CountableRule.pullbackSeededIndividual_candidateAction,
    mapSingleIndividualWorld,codeTime_replaceIndividualValue,codePresent,candidatePresent_replaceIndividualValue]

lemma CountableRule.pullbackSeededIndividual_earliest (π : CountableRule Seed) (i : ℕ)
    (g : Seed → ℝ → ℝ) (v : CompleteWorld Seed) (k : ℕ) :
    FirstAcceptance.Earliest (π.pullbackSeededIndividual i g).codeAccepted codeTime v k ↔
      FirstAcceptance.Earliest π.codeAccepted codeTime (mapSingleIndividualWorld i (g v.2.2.2) v) k := by
  simp only [FirstAcceptance.Earliest,CountableRule.pullbackSeededIndividual_codeAccepted,
    mapSingleIndividualWorld,codeTime_replaceIndividualValue]

lemma CountableRule.pullbackSeededIndividual_hasFirst (π : CountableRule Seed) (i : ℕ)
    (g : Seed → ℝ → ℝ) (v : CompleteWorld Seed) :
    FirstAcceptance.HasFirstIfAccepted (π.pullbackSeededIndividual i g).codeAccepted codeTime v ↔
      FirstAcceptance.HasFirstIfAccepted π.codeAccepted codeTime (mapSingleIndividualWorld i (g v.2.2.2) v) := by
  simp only [FirstAcceptance.HasFirstIfAccepted,CountableRule.pullbackSeededIndividual_codeAccepted,
    CountableRule.pullbackSeededIndividual_earliest]

lemma CountableRule.pullbackSeededIndividual_selectedCode (π : CountableRule Seed) (i : ℕ)
    (g : Seed → ℝ → ℝ) (v : CompleteWorld Seed) :
    FirstAcceptance.selectedCode (π.pullbackSeededIndividual i g).codeAccepted codeTime v=
      FirstAcceptance.selectedCode π.codeAccepted codeTime (mapSingleIndividualWorld i (g v.2.2.2) v) := by
  exact FirstAcceptance.selectedCode_timeScale (h := 1) zero_lt_one
    (fun k => π.pullbackSeededIndividual_codeAccepted i g v k)
    (fun k _ => by simpa only [one_mul,mapSingleIndividualWorld] using
      (codeTime_replaceIndividualValue i (v,g v.2.2.2 (v.2.1 i)) k).symm)

lemma CountableRule.pullbackSeededIndividual_duration (π : CountableRule Seed) (i : ℕ)
    (g : Seed → ℝ → ℝ) (v : CompleteWorld Seed) :
    (π.pullbackSeededIndividual i g).realizedDuration v=
      π.realizedDuration (mapSingleIndividualWorld i (g v.2.2.2) v) := by
  simp only [CountableRule.realizedDuration,FirstAcceptance.stoppingTime,
    CountableRule.pullbackSeededIndividual_selectedCode,mapSingleIndividualWorld,codeTime_replaceIndividualValue]

lemma CountableRule.pullbackSeededIndividual_reward (π : CountableRule Seed) (i : ℕ)
    (g : Seed → ℝ → ℝ) (a : ℝ) (v : CompleteWorld Seed) :
    π.realizedReward a (mapSingleIndividualWorld i (g v.2.2.2) v)=
      (π.pullbackSeededIndividual i g).realizedReward a v+
        (π.pullbackSeededIndividual i g).individualSelectionIndicator i v*(g v.2.2.2 (v.2.1 i)-v.2.1 i) := by
  have hCode := (π.pullbackSeededIndividual_selectedCode i g v).trans
    (π.pullbackSingleIndividual_selectedCode i (g v.2.2.2) v).symm
  simpa only [CountableRule.individualSelectionIndicator_eq_code,CountableRule.realizedReward,FirstAcceptance.reward,hCode] using
    π.pullbackSingleIndividual_reward i (g v.2.2.2) a v

end ProphetSecretary.Limiting.CountableInstance
