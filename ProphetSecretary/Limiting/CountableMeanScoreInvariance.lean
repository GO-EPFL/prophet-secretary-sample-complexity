import ProphetSecretary.Limiting.CountableMeanDurationCoupling

/-!
# Individual zero-score responses survive mean contraction

Every untouched coordinate and its score are preserved by the actual mean
coupling. The contracted coordinate is deterministic, so every centered
score is zero on its law. Canonical duration uniqueness therefore preserves
the complete collection of individual zero duration-score responses.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

theorem canonical_individual_durationScores_zero_after_contraction
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c)
    (hScores : ∀ (j : ℕ) (φ : ℝ → ℝ), Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals j : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 j)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0)
    (i k : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ) (hb : ∀ x, |φ x| ≤ 1)
    (hMean : (∫ x, φ x ∂((B.contractIndividual i).individuals k : Measure ℝ))=0) :
    (∫ v : CompleteWorld Unit, φ (v.2.1 k)*((B.contractIndividual i).valueRule w c).realizedDuration v
      ∂(B.contractIndividual i).completeWorldLaw (Measure.dirac ()))=0 := by
  let Q := B.contractIndividual i
  by_cases hki : k=i
  · subst k
    have hφMean : φ (B.individualMean i)=0 := by
      rw [B.contractIndividual_individual_law] at hMean
      simpa only [integral_dirac] using hMean
    have hValue : ∀ᵐ x ∂(Q.individuals i : Measure ℝ), x=B.individualMean i := by
      change ∀ᵐ x ∂((B.contractIndividual i).individuals i : Measure ℝ), x=B.individualMean i
      rw [B.contractIndividual_individual_law]
      exact (ae_dirac_iff (measurableSet_singleton _)).mpr rfl
    have hMP : MeasurePreserving (fun v : CompleteWorld Unit => v.2.1 i)
        (Q.completeWorldLaw (Measure.dirac ())) (Q.individuals i : Measure ℝ) :=
      (Q.individualValue_measurePreserving i).comp (measurePreserving_fst.comp measurePreserving_snd)
    calc
      _ = ∫ _ : CompleteWorld Unit, (0 : ℝ) ∂Q.completeWorldLaw (Measure.dirac ()) := by
        apply integral_congr_ae
        filter_upwards [hMP.quasiMeasurePreserving.ae hValue] with v hv
        rw [hv,hφMean,zero_mul]
      _ = 0 := by simp only [integral_zero]
  · have hMarginal : (Q.individuals k : Measure ℝ)=(B.individuals k : Measure ℝ) :=
      congrArg (fun q : ProbabilityMeasure ℝ => (q : Measure ℝ)) (B.contractIndividual_other i k hki)
    have hOldMean : (∫ x, φ x ∂(B.individuals k : Measure ℝ))=0 := by
      change (∫ x, φ x ∂(Q.individuals k : Measure ℝ))=0 at hMean
      rwa [hMarginal] at hMean
    have hMeas : Measurable (fun v : CompleteWorld Unit => φ (v.2.1 k)) :=
      hφ.comp ((measurable_pi_apply k).comp (measurable_fst.comp measurable_snd))
    have hInt : Integrable (fun v : CompleteWorld Unit => φ (v.2.1 k)) (B.completeWorldLaw (Measure.dirac ())) :=
      Integrable.of_bound hMeas.aestronglyMeasurable 1 (Eventually.of_forall (fun v => by
        rw [Real.norm_eq_abs]
        exact hb _))
    have hInvariant : ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
        φ ((replaceIndividualValue i (v,B.individualMean i)).2.1 k)=φ (v.2.1 k) :=
      Eventually.of_forall (fun v => by simp only [replaceIndividualValue,Function.update_of_ne hki])
    exact (B.canonical_durationScore_contractIndividual hZero hw hc i (hScores i) _ hMeas hInt hInvariant).2.trans
      (hScores k φ hφ hb hOldMean)

end ProphetSecretary.Limiting.CountableInstance
