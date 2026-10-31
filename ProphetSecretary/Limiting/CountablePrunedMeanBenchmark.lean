import ProphetSecretary.Limiting.CountablePrunedMeanPrefix
import ProphetSecretary.Limiting.CountableMeanPrefixMaximum
import ProphetSecretary.Limiting.OmissionTailLevel

/-!
# Benchmark error for the pruned mean prefixes

After contracting the first N individuals and deleting the first N+1 cloud
bands, every remaining anonymous mark is at most the Nth cutoff. The full
maximum is at most the deterministic prefix maximum plus the original
omitted-individual excess maximum and that cutoff. The bound is integrated
under the actual deletion pushforward; its tail law is unchanged by the
finite individual contractions.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

lemma maximum_eraseFirstBands_meanPrefix_le (B : CountableInstance) (hTerminal : B.terminal=0)
    (N : ℕ) (v : CompleteWorld Unit)
    (hValues : ∀ i, v.2.1 i≤((B.meanContractPrefix N).cap : ℝ))
    (hPrefix : ∀ i : Fin N, v.2.1 i.val=B.individualMean i.val)
    (hMarks : ∀ k j, ((v.1 k).2 j).2 ∈ (B.meanContractPrefix N).markBand k) :
    (B.meanContractPrefix N).maximum
        ((eraseFirstBandsWorld N v).1,(eraseFirstBandsWorld N v).2.1) ≤
      B.meanPrefixMaximum N+(B.meanContractPrefix N).individualTailExcessMaximum N v.2.1+
        (B.meanContractPrefix N).markCutoff N := by
  let Q := B.meanContractPrefix N
  let Z := Q.individualTailExcessMaximum N v.2.1
  let m := B.meanPrefixMaximum N
  let δ := Q.markCutoff N
  have hQTerminal : Q.terminal=0 := (B.meanContractPrefix_terminal N).trans hTerminal
  have hZ : 0≤Z := (Q.individualTailExcessMaximum_bounds_of_cap N v.2.1 hValues).1
  have hm : 0≤m := B.meanPrefixMaximum_nonnegative N
  have hδ : 0≤δ := Q.terminal.property.trans (Q.terminal_lt_markCutoff N).le
  have hBound : 0≤m+Z+δ := add_nonneg (add_nonneg hm hZ) hδ
  have hBase : (Q.terminal : ℝ)≤m+Z+δ := by
    rw [hQTerminal,NNReal.coe_zero]
    exact hBound
  apply countableMaximum_le hBase hBound
  intro k
  apply max_le
  · change v.2.1 k≤m+Z+δ
    by_cases hk : k<N
    · rw [hPrefix ⟨k,hk⟩]
      have hM := Model.Instance.le_maximum (fun i : Fin N => B.individualMean i.val) ⟨k,hk⟩
      exact hM.trans ((le_add_of_nonneg_right hZ).trans (le_add_of_nonneg_right hδ))
    · have hTail := Q.individual_value_le_tail_level N v.2.1 hValues k (le_of_not_gt hk)
      rw [hQTerminal,NNReal.coe_zero,add_zero] at hTail
      exact hTail.trans ((le_add_of_nonneg_left hm).trans (le_add_of_nonneg_right hδ))
  · change bandMaximum (if k≤N then emptyConfiguration else v.1 k)≤m+Z+δ
    by_cases hk : k≤N
    · rw [if_pos hk]
      apply Model.Instance.maximum_le _ hBound
      intro j
      exact Fin.elim0 j
    · rw [if_neg hk]
      have hBand : bandMaximum (v.1 k)≤δ := by
        apply Model.Instance.maximum_le _ hδ
        intro j
        have hNot : ((v.1 k).2 j).2 ∉ Q.firstBandWindow N := fun h =>
          Set.disjoint_left.mp (Q.markBand_disjoint_firstBandWindow (lt_of_not_ge hk)) (hMarks k j) h
        rw [Q.firstBandWindow_eq_tail] at hNot
        exact le_of_not_gt hNot
      exact hBand.trans (le_add_of_nonneg_left (add_nonneg hm hZ))

theorem prunedMeanPrefix_expectedMaximum_le (B : CountableInstance) (hTerminal : B.terminal=0) (N : ℕ) :
    (B.prunedMeanPrefix N).expectedMaximum ≤
      B.meanPrefixMaximum N+B.expectedIndividualTailExcessMaximum N+B.markCutoff N := by
  let Q := B.meanContractPrefix N
  let D := B.prunedMeanPrefix N
  let F : CompleteWorld Unit → ℝ := fun v => Q.maximum
    ((eraseFirstBandsWorld N v).1,(eraseFirstBandsWorld N v).2.1)
  have hMP := Q.eraseFirstBandsWorld_measurePreserving N (Measure.dirac ())
  have hValues : MeasurePreserving (fun v : CompleteWorld Unit => v.2.1)
      (Q.completeWorldLaw (Measure.dirac ())) Q.individualValuesLaw :=
    measurePreserving_fst.comp measurePreserving_snd
  have hPrefix (i : Fin N) : ∀ᵐ v : CompleteWorld Unit ∂Q.completeWorldLaw (Measure.dirac ()),
      v.2.1 i.val=B.individualMean i.val := by
    have hLaw : ∀ᵐ x ∂(Q.individuals i.val : Measure ℝ), x=B.individualMean i.val := by
      rw [B.meanContractPrefix_contracted_laws N i.val i.isLt]
      exact (ae_dirac_iff (measurableSet_singleton _)).mpr rfl
    exact ((Q.individualValue_measurePreserving i.val).comp hValues).quasiMeasurePreserving.ae hLaw
  have hMarks := (Measure.quasiMeasurePreserving_fst (μ := Q.bandConfigurationsLaw)
    (ν := Q.individualWorldLaw (Measure.dirac ()))).ae Q.bandConfigurations_marks_in_band
  have hDMeas : Measurable (fun v : CompleteWorld Unit => D.maximum (v.1,v.2.1)) :=
    D.measurable_maximum.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hDInt : Integrable (fun v : CompleteWorld Unit => D.maximum (v.1,v.2.1))
      (D.completeWorldLaw (Measure.dirac ())) :=
    (D.value_projection_measurePreserving (Measure.dirac ())).integrable_comp_of_integrable D.integrable_maximum
  have hFInt : Integrable F (Q.completeWorldLaw (Measure.dirac ())) := hMP.integrable_comp_of_integrable hDInt
  have hMap := hMP.hasLaw.integral_comp hDMeas.aestronglyMeasurable
  have hValue := (D.value_projection_measurePreserving (Measure.dirac ())).hasLaw.integral_comp D.measurable_maximum.aestronglyMeasurable
  have hIdentity : (B.prunedMeanPrefix N).expectedMaximum=∫ v, F v ∂Q.completeWorldLaw (Measure.dirac ()) :=
    hValue.symm.trans hMap.symm
  have hTailInt : Integrable (fun v : CompleteWorld Unit => Q.individualTailExcessMaximum N v.2.1)
      (Q.completeWorldLaw (Measure.dirac ())) :=
    hValues.integrable_comp_of_integrable (Q.integrable_individualTailExcessMaximum N)
  have hTailMean : (∫ v : CompleteWorld Unit, Q.individualTailExcessMaximum N v.2.1
      ∂Q.completeWorldLaw (Measure.dirac ()))=Q.expectedIndividualTailExcessMaximum N :=
    hValues.hasLaw.integral_comp (Q.measurable_individualTailExcessMaximum N).aestronglyMeasurable
  have hUpperInt : Integrable (fun v : CompleteWorld Unit =>
      B.meanPrefixMaximum N+Q.individualTailExcessMaximum N v.2.1+Q.markCutoff N)
      (Q.completeWorldLaw (Measure.dirac ())) :=
    ((integrable_const (B.meanPrefixMaximum N)).add hTailInt).add (integrable_const (Q.markCutoff N))
  have hPoint : F ≤ᵐ[Q.completeWorldLaw (Measure.dirac ())] (fun v =>
      B.meanPrefixMaximum N+Q.individualTailExcessMaximum N v.2.1+Q.markCutoff N) := by
    filter_upwards [ae_all_iff.mpr hPrefix,hValues.quasiMeasurePreserving.ae Q.individual_values_supported,hMarks]
      with v hp hv hm
    exact B.maximum_eraseFirstBands_meanPrefix_le hTerminal N v (fun i => (hv i).2) hp hm
  have hBound := integral_mono_ae hFInt hUpperInt hPoint
  have hUpperMean : (∫ v : CompleteWorld Unit,
      B.meanPrefixMaximum N+Q.individualTailExcessMaximum N v.2.1+Q.markCutoff N
        ∂Q.completeWorldLaw (Measure.dirac ()))=
      B.meanPrefixMaximum N+Q.expectedIndividualTailExcessMaximum N+Q.markCutoff N := by
    rw [integral_add (f := fun v : CompleteWorld Unit => B.meanPrefixMaximum N+Q.individualTailExcessMaximum N v.2.1)
        (g := fun _ => Q.markCutoff N) ((integrable_const _).add hTailInt) (integrable_const _),
      integral_add (f := fun _ : CompleteWorld Unit => B.meanPrefixMaximum N)
        (g := fun v => Q.individualTailExcessMaximum N v.2.1) (integrable_const _) hTailInt,hTailMean]
    simp only [integral_const,probReal_univ,one_smul]
  have hFinal := hIdentity.trans_le (hBound.trans_eq hUpperMean)
  simpa only [Q,B.meanContractPrefix_expected_tail_eq N,markCutoff,meanContractPrefix_terminal] using hFinal

end ProphetSecretary.Limiting.CountableInstance
