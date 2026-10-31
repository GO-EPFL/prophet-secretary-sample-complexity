import ProphetSecretary.Limiting.CountablePolicy
import ProphetSecretary.Model.Truncation

/-!
# Causal transformations of individual observations

Only the current individual value and values in the observed individual
history are mapped. Anonymous observations, identities, clocks, history
presence and the independent seed are unchanged. The complete-world map is
analytical; its future coordinates are never supplied to a callback.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

noncomputable def mapIndividualHistory (g : ℝ → ℝ) (H : IndividualHistory) : IndividualHistory :=
  fun i => Model.mapObservationValues g (H i)

lemma mapIndividualHistory_actual (g : ℝ → ℝ) (x u : ℕ → ℝ) (t : ℝ) :
    mapIndividualHistory g (individualHistory x u t)=individualHistory (g ∘ x) u t := by
  funext i
  by_cases hi : u i<t <;> simp only [mapIndividualHistory,individualHistory,hi,if_true,if_false,Model.mapObservationValues,Function.comp_apply]

lemma measurable_mapIndividualHistory {g : ℝ → ℝ} (hg : Measurable g) : Measurable (mapIndividualHistory g) :=
  measurable_pi_lambda _ fun i => (Model.measurable_mapObservationValues hg).comp (measurable_pi_apply i)

noncomputable def mapIndividualWorld (g : ℝ → ℝ) (v : CompleteWorld Seed) : CompleteWorld Seed :=
  (v.1,(g ∘ v.2.1,v.2.2))

lemma measurable_mapIndividualWorld [MeasurableSpace Seed] {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (mapIndividualWorld (Seed:=Seed) g) :=
  measurable_fst.prodMk ((measurable_pi_lambda _ (fun i => hg.comp
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))).prodMk (measurable_snd.comp measurable_snd))

noncomputable def CountableRule.pullbackIndividualValues (π : CountableRule Seed) (g : ℝ → ℝ) : CountableRule Seed where
  individual r t i x H ξ := π.individual r t i (g x) (mapIndividualHistory g H) ξ
  poisson r t x H ξ := π.poisson r t x (mapIndividualHistory g H) ξ

lemma CountableRule.pullbackIndividualValues_isMeasurable [MeasurableSpace Seed]
    (π : CountableRule Seed) (hπ : π.IsMeasurable) {g : ℝ → ℝ} (hg : Measurable g) :
    (π.pullbackIndividualValues g).IsMeasurable := by
  have hH := measurable_mapIndividualHistory hg
  refine ⟨?_,?_⟩
  · exact hπ.1.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
      (measurable_snd.snd.fst.prodMk ((hg.comp measurable_snd.snd.snd.fst).prodMk
        ((hH.comp measurable_snd.snd.snd.snd.fst).prodMk measurable_snd.snd.snd.snd.snd)))))
  · exact hπ.2.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
      ((hH.comp measurable_snd.snd.fst).prodMk measurable_snd.snd.snd)))

lemma CountableRule.pullbackIndividualValues_candidateAction (π : CountableRule Seed) (g : ℝ → ℝ)
    (v : CompleteWorld Seed) (i : Candidate) :
    (π.pullbackIndividualValues g).candidateAction v i=π.candidateAction (mapIndividualWorld g v) i := by
  cases i <;> simp only [CountableRule.candidateAction,candidatePoint,CountableRule.pullbackIndividualValues,
    mapIndividualWorld,mapIndividualHistory_actual,Function.comp_apply]

lemma codeTime_mapIndividualWorld (g : ℝ → ℝ) (v : CompleteWorld Seed) (i : ℕ) :
    codeTime (mapIndividualWorld g v) i=codeTime v i := by
  cases h : candidateEnumeration.symm i <;> simp only [codeTime,codePoint,h,candidatePoint,mapIndividualWorld]

lemma codePresent_mapIndividualWorld (g : ℝ → ℝ) (v : CompleteWorld Seed) (i : ℕ) :
    codePresent (mapIndividualWorld g v) i=codePresent v i := by
  cases h : candidateEnumeration.symm i <;> simp only [codePresent,h,candidatePresent,mapIndividualWorld]

lemma CountableRule.pullbackIndividualValues_codeAccepted (π : CountableRule Seed) (g : ℝ → ℝ)
    (v : CompleteWorld Seed) (i : ℕ) :
    (π.pullbackIndividualValues g).codeAccepted v i=π.codeAccepted (mapIndividualWorld g v) i := by
  simp only [CountableRule.codeAccepted,codePresent_mapIndividualWorld,codeTime_mapIndividualWorld,
    CountableRule.pullbackIndividualValues_candidateAction]

lemma CountableRule.pullbackIndividualValues_earliest (π : CountableRule Seed) (g : ℝ → ℝ)
    (v : CompleteWorld Seed) (i : ℕ) :
    FirstAcceptance.Earliest (π.pullbackIndividualValues g).codeAccepted codeTime v i ↔
      FirstAcceptance.Earliest π.codeAccepted codeTime (mapIndividualWorld g v) i := by
  simp only [FirstAcceptance.Earliest,CountableRule.pullbackIndividualValues_codeAccepted,codeTime_mapIndividualWorld]

lemma CountableRule.pullbackIndividualValues_hasFirst (π : CountableRule Seed) (g : ℝ → ℝ)
    (v : CompleteWorld Seed) :
    FirstAcceptance.HasFirstIfAccepted (π.pullbackIndividualValues g).codeAccepted codeTime v ↔
      FirstAcceptance.HasFirstIfAccepted π.codeAccepted codeTime (mapIndividualWorld g v) := by
  simp only [FirstAcceptance.HasFirstIfAccepted,CountableRule.pullbackIndividualValues_codeAccepted,
    CountableRule.pullbackIndividualValues_earliest]

lemma CountableRule.pullbackIndividualValues_selectedCode (π : CountableRule Seed) (g : ℝ → ℝ)
    (v : CompleteWorld Seed) :
    FirstAcceptance.selectedCode (π.pullbackIndividualValues g).codeAccepted codeTime v=
      FirstAcceptance.selectedCode π.codeAccepted codeTime (mapIndividualWorld g v) := by
  by_cases h : ∃ i, FirstAcceptance.Earliest (π.pullbackIndividualValues g).codeAccepted codeTime v i
  · obtain ⟨i,hi⟩ := h
    rw [(FirstAcceptance.selectedCode_eq_succ_iff _ _ _ i).mpr hi,
      (FirstAcceptance.selectedCode_eq_succ_iff _ _ _ i).mpr ((π.pullbackIndividualValues_earliest g v i).mp hi)]
  · have h' : ¬∃ i, FirstAcceptance.Earliest π.codeAccepted codeTime (mapIndividualWorld g v) i := by
      intro hi
      obtain ⟨i,hi⟩ := hi
      exact h ⟨i,(π.pullbackIndividualValues_earliest g v i).mpr hi⟩
    rw [(FirstAcceptance.selectedCode_eq_zero_iff _ _ _).mpr h,(FirstAcceptance.selectedCode_eq_zero_iff _ _ _).mpr h']

lemma CountableRule.pullbackIndividualValues_duration (π : CountableRule Seed) (g : ℝ → ℝ)
    (v : CompleteWorld Seed) :
    (π.pullbackIndividualValues g).realizedDuration v=π.realizedDuration (mapIndividualWorld g v) := by
  simp only [CountableRule.realizedDuration,FirstAcceptance.stoppingTime,
    CountableRule.pullbackIndividualValues_selectedCode,codeTime_mapIndividualWorld]

lemma codeValue_mapIndividualWorld_le (g : ℝ → ℝ) (v : CompleteWorld Seed)
    (hDown : ∀ i, g (v.2.1 i)≤v.2.1 i) (j : ℕ) :
    codeValue (mapIndividualWorld g v) j≤codeValue v j := by
  cases h : candidateEnumeration.symm j with
  | inl i => simpa only [codeValue,codePoint,h,candidatePoint,mapIndividualWorld,Function.comp_apply] using hDown i
  | inr kj => simp only [codeValue,codePoint,h,candidatePoint,mapIndividualWorld,le_refl]

lemma CountableRule.pullbackIndividualValues_reward_le (π : CountableRule Seed) (g : ℝ → ℝ)
    (a : ℝ) (v : CompleteWorld Seed) (hDown : ∀ i, g (v.2.1 i)≤v.2.1 i) :
    π.realizedReward a (mapIndividualWorld g v)≤(π.pullbackIndividualValues g).realizedReward a v := by
  unfold CountableRule.realizedReward FirstAcceptance.reward
  rw [CountableRule.pullbackIndividualValues_selectedCode]
  split_ifs
  · exact le_rfl
  · exact codeValue_mapIndividualWorld_le g v hDown _

end ProphetSecretary.Limiting.CountableInstance
