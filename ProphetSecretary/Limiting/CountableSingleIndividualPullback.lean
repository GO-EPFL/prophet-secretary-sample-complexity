import ProphetSecretary.Limiting.CountableIndividualMap
import ProphetSecretary.Limiting.CountableIndividualPullback
import ProphetSecretary.Limiting.FirstAcceptanceTimeScaling

/-!
# Causal pullback of a single individual-value map

The candidate identity determines which current value and which already
observed history entry are transformed. History presence and arrival times
are retained, including observed zeros. Anonymous past information is copied
unchanged. Actual first selection and duration agree with execution on the
mapped complete world.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

noncomputable def mapSingleIndividualHistory (i : ℕ) (g : ℝ → ℝ) (H : IndividualHistory) : IndividualHistory :=
  fun j => if j=i then Model.mapObservationValues g (H j) else H j

lemma mapSingleIndividualHistory_actual (i : ℕ) (g : ℝ → ℝ) (x u : ℕ → ℝ) (t : ℝ) :
    mapSingleIndividualHistory i g (individualHistory x u t)=
      individualHistory (Function.update x i (g (x i))) u t := by
  funext j
  by_cases hji : j=i
  · subst j
    by_cases ht : u i<t <;> simp only [mapSingleIndividualHistory,individualHistory,ht,
      if_true,if_false,Function.update_self,Model.mapObservationValues]
  · simp only [mapSingleIndividualHistory,if_neg hji,individualHistory,Function.update_of_ne hji]

lemma measurable_mapSingleIndividualHistory (i : ℕ) {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (mapSingleIndividualHistory i g) := by
  apply measurable_pi_lambda
  intro j
  by_cases hji : j=i
  · simpa only [mapSingleIndividualHistory,if_pos hji,Function.comp_def] using
      (Model.measurable_mapObservationValues hg).comp (measurable_pi_apply j)
  · simpa only [mapSingleIndividualHistory,if_neg hji] using
      (measurable_pi_apply j : Measurable (fun H : IndividualHistory => H j))

noncomputable def CountableRule.pullbackSingleIndividual (π : CountableRule Seed) (i : ℕ) (g : ℝ → ℝ) : CountableRule Seed where
  individual r t j x H ξ := π.individual r t j (if j=i then g x else x) (mapSingleIndividualHistory i g H) ξ
  poisson r t x H ξ := π.poisson r t x (mapSingleIndividualHistory i g H) ξ

lemma CountableRule.pullbackSingleIndividual_isMeasurable [MeasurableSpace Seed]
    (π : CountableRule Seed) (hπ : π.IsMeasurable) (i : ℕ) {g : ℝ → ℝ} (hg : Measurable g) :
    (π.pullbackSingleIndividual i g).IsMeasurable := by
  have hH := measurable_mapSingleIndividualHistory i hg
  have hCurrent : Measurable (fun z : Seed × (ℝ × (ℕ × (ℝ × (IndividualHistory × Measure Point)))) =>
      if z.2.2.1=i then g z.2.2.2.1 else z.2.2.2.1) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd.snd.fst measurable_const)
      (hg.comp measurable_snd.snd.snd.fst) measurable_snd.snd.snd.fst
  refine ⟨?_,?_⟩
  · exact hπ.1.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
      (measurable_snd.snd.fst.prodMk (hCurrent.prodMk
        ((hH.comp measurable_snd.snd.snd.snd.fst).prodMk measurable_snd.snd.snd.snd.snd)))))
  · exact hπ.2.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
      ((hH.comp measurable_snd.snd.fst).prodMk measurable_snd.snd.snd)))

lemma CountableRule.pullbackSingleIndividual_candidateAction (π : CountableRule Seed)
    (i : ℕ) (g : ℝ → ℝ) (v : CompleteWorld Seed) (k : Candidate) :
    (π.pullbackSingleIndividual i g).candidateAction v k=
      π.candidateAction (mapSingleIndividualWorld i g v) k := by
  cases k with
  | inl j =>
    by_cases hji : j=i
    · subst j
      simp only [CountableRule.candidateAction,candidatePoint,CountableRule.pullbackSingleIndividual,
        mapSingleIndividualWorld,replaceIndividualValue,mapSingleIndividualHistory_actual,ite_true,Function.update_self]
    · simp only [CountableRule.candidateAction,candidatePoint,CountableRule.pullbackSingleIndividual,
        mapSingleIndividualWorld,replaceIndividualValue,mapSingleIndividualHistory_actual,if_neg hji,Function.update_of_ne hji]
  | inr kj =>
    simp only [CountableRule.candidateAction,candidatePoint,CountableRule.pullbackSingleIndividual,
      mapSingleIndividualWorld,replaceIndividualValue,mapSingleIndividualHistory_actual]

lemma CountableRule.pullbackSingleIndividual_codeAccepted (π : CountableRule Seed)
    (i : ℕ) (g : ℝ → ℝ) (v : CompleteWorld Seed) (k : ℕ) :
    (π.pullbackSingleIndividual i g).codeAccepted v k ↔
      π.codeAccepted (mapSingleIndividualWorld i g v) k := by
  simp only [CountableRule.codeAccepted,CountableRule.pullbackSingleIndividual_candidateAction,
    mapSingleIndividualWorld,codeTime_replaceIndividualValue,codePresent,candidatePresent_replaceIndividualValue]

lemma CountableRule.pullbackSingleIndividual_earliest (π : CountableRule Seed)
    (i : ℕ) (g : ℝ → ℝ) (v : CompleteWorld Seed) (k : ℕ) :
    FirstAcceptance.Earliest (π.pullbackSingleIndividual i g).codeAccepted codeTime v k ↔
      FirstAcceptance.Earliest π.codeAccepted codeTime (mapSingleIndividualWorld i g v) k := by
  simp only [FirstAcceptance.Earliest,CountableRule.pullbackSingleIndividual_codeAccepted,
    mapSingleIndividualWorld,codeTime_replaceIndividualValue]

lemma CountableRule.pullbackSingleIndividual_hasFirst (π : CountableRule Seed)
    (i : ℕ) (g : ℝ → ℝ) (v : CompleteWorld Seed) :
    FirstAcceptance.HasFirstIfAccepted (π.pullbackSingleIndividual i g).codeAccepted codeTime v ↔
      FirstAcceptance.HasFirstIfAccepted π.codeAccepted codeTime (mapSingleIndividualWorld i g v) := by
  simp only [FirstAcceptance.HasFirstIfAccepted,CountableRule.pullbackSingleIndividual_codeAccepted,
    CountableRule.pullbackSingleIndividual_earliest]

lemma CountableRule.pullbackSingleIndividual_selectedCode (π : CountableRule Seed)
    (i : ℕ) (g : ℝ → ℝ) (v : CompleteWorld Seed) :
    FirstAcceptance.selectedCode (π.pullbackSingleIndividual i g).codeAccepted codeTime v=
      FirstAcceptance.selectedCode π.codeAccepted codeTime (mapSingleIndividualWorld i g v) := by
  exact FirstAcceptance.selectedCode_timeScale (h := 1) zero_lt_one
    (fun k => π.pullbackSingleIndividual_codeAccepted i g v k)
    (fun k _ => by simpa only [one_mul,mapSingleIndividualWorld] using (codeTime_replaceIndividualValue i (v,g (v.2.1 i)) k).symm)

lemma CountableRule.pullbackSingleIndividual_duration (π : CountableRule Seed)
    (i : ℕ) (g : ℝ → ℝ) (v : CompleteWorld Seed) :
    (π.pullbackSingleIndividual i g).realizedDuration v=
      π.realizedDuration (mapSingleIndividualWorld i g v) := by
  simp only [CountableRule.realizedDuration,FirstAcceptance.stoppingTime,
    CountableRule.pullbackSingleIndividual_selectedCode,mapSingleIndividualWorld,codeTime_replaceIndividualValue]

end ProphetSecretary.Limiting.CountableInstance
