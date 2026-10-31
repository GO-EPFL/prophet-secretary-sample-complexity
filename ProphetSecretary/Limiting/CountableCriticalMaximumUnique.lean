import ProphetSecretary.Limiting.CountableCriticalPoissonMaximum
import ProphetSecretary.Limiting.CountableCriticalIndividualTie
import ProphetSecretary.Limiting.CountableMaximumAttainment

/-!
# Uniqueness of the positive realized maximum at criticality

This is the maximum-uniqueness assertion of paper `lem:location`. Individual
competing ties and Poisson-only ties are excluded on one countable almost
sure event. The comparison uses actual present occurrences, including every
zero-valued individual identity.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

lemma competingMaximum_dominates_other_ae (B : CountableInstance) (i : ℕ) :
    ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      ∀ d : Candidate, candidatePresent v d → d≠Sum.inl i →
        (candidatePoint v d).2≤B.competingMaximum i v := by
  let hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), (0 : ℝ)∈Icc (0 : ℝ) B.cap :=
    Eventually.of_forall (fun _ => ⟨le_rfl,B.cap.property⟩)
  let Q := B.mapIndividual i (fun _ => (0 : ℝ)) measurable_const hSupport
  have hMP := B.mapSingleIndividualWorld_measurePreserving i (fun _ => (0 : ℝ)) measurable_const hSupport (Measure.dirac ())
  filter_upwards [hMP.quasiMeasurePreserving.ae (Q.candidate_value_le_maximum (Measure.dirac ()))] with v hv d hd hNe
  have hPresent := (candidatePresent_replaceIndividualValue i (v,0) d).mpr hd
  have h := hv d hPresent
  change (candidatePoint (replaceIndividualValue i (v,0)) d).2≤B.competingMaximum i v at h
  rw [candidatePoint_replaceIndividualValue_of_ne i (v,0) d hNe] at h
  exact h

/-- At a critical interior pair, two present occurrences attaining a positive
realized maximum are the same occurrence. -/
theorem critical_positive_maximum_unique (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) :
    ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      ∀ d e : Candidate, candidatePresent v d → candidatePresent v e →
        (candidatePoint v d).2=B.maximum (v.1,v.2.1) →
        (candidatePoint v e).2=B.maximum (v.1,v.2.1) →
        0<B.maximum (v.1,v.2.1) → d=e := by
  filter_upwards [B.critical_poisson_maximum_unique hw hc hCritical,
    ae_all_iff.mpr (fun i => B.critical_individual_no_competing_ties hw hc hCritical i),
    ae_all_iff.mpr (fun i => B.competingMaximum_dominates_other_ae i),
    ae_all_iff.mpr (fun i => B.maximum_eq_max_competing_ae (Measure.dirac ()) i)]
      with v hPoisson hIndividual hOther hMax
  have hIndividualUnique (i : ℕ) (e : Candidate) (he : candidatePresent v e)
      (hiMax : v.2.1 i=B.maximum (v.1,v.2.1))
      (heMax : (candidatePoint v e).2=B.maximum (v.1,v.2.1))
      (hPos : 0<B.maximum (v.1,v.2.1)) : Sum.inl i=e := by
    by_contra hNe
    have hLower : B.maximum (v.1,v.2.1)≤B.competingMaximum i v :=
      heMax.symm.trans_le (hOther i e he (Ne.symm hNe))
    have hUpper : B.competingMaximum i v≤B.maximum (v.1,v.2.1) :=
      (le_max_right _ _).trans_eq (hMax i).symm
    have hComp : B.competingMaximum i v=B.maximum (v.1,v.2.1) := le_antisymm hUpper hLower
    exact hIndividual i (hPos.trans_eq hiMax.symm) (hiMax.trans hComp.symm)
  intro d e hd he hdMax heMax hPos
  cases d with
  | inl i => exact hIndividualUnique i e he hdMax heMax hPos
  | inr kj =>
    cases e with
    | inl i => exact (hIndividualUnique i (Sum.inr kj) hd heMax hdMax hPos).symm
    | inr lm =>
      change kj.2<(v.1 kj.1).1 at hd
      change lm.2<(v.1 lm.1).1 at he
      have hD : ((v.1 kj.1).2 ⟨kj.2,hd⟩).2=B.maximum (v.1,v.2.1) := by
        simpa only [candidatePoint,configurationPoint,dif_pos hd] using hdMax
      have hE : ((v.1 lm.1).2 ⟨lm.2,he⟩).2=B.maximum (v.1,v.2.1) := by
        simpa only [candidatePoint,configurationPoint,dif_pos he] using heMax
      have h := hPoisson kj.1 lm.1 ⟨kj.2,hd⟩ ⟨lm.2,he⟩ hD hE hPos
      exact congrArg Sum.inr (Prod.ext h.1 h.2)

/-- Paper `lem:location`: uniqueness of every positive maximal occurrence and
its individual-variable conditional selection identity. -/
theorem critical_location (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) :
    (∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      ∀ d e : Candidate, candidatePresent v d → candidatePresent v e →
        (candidatePoint v d).2=B.maximum (v.1,v.2.1) →
        (candidatePoint v e).2=B.maximum (v.1,v.2.1) →
        0<B.maximum (v.1,v.2.1) → d=e) ∧
    ∀ i, ∀ᵐ x ∂(B.individuals i : Measure ℝ), 0<x →
      B.individualLocationSelection w c i x=ProphetSecretary.Model.optimalCompetitiveRatio*
        B.individualLocationProphet i x :=
  ⟨B.critical_positive_maximum_unique hw hc hCritical,B.critical_individual_location hw hc hCritical⟩

end ProphetSecretary.Limiting.CountableInstance
