import ProphetSecretary.Limiting.CountableLocalFiniteness
import ProphetSecretary.Limiting.CountableCompetingMaximumLaw
import ProphetSecretary.Limiting.CountableIndividualMap

/-!
# Attainment of a realized maximum above the reserve

Only finitely many actual occurrences exceed any level strictly above the
reserve. If the maximum exceeds the reserve, the occurrences above an
intermediate level therefore contain an attaining occurrence. Replacing one
individual by zero supplies the corresponding statement for its competing
maximum. This bridges uniqueness among actual positive maximum occurrences
to the analytical individual/competing no-tie premise in the location identity.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

lemma maximum_le_of_codeValues (B : CountableInstance) (v : CompleteWorld Seed) (z : ℝ)
    (ha : (B.terminal : ℝ)≤z) (hz : 0≤z)
    (hOffers : ∀ i, codePresent v i → codeValue v i≤z) : B.maximum (v.1,v.2.1)≤z := by
  apply countableMaximum_le ha hz
  intro k
  apply max_le
  · have h := hOffers (candidateEnumeration (Sum.inl k)) (individual_candidate_present v k)
    simpa only [codeValue,individual_candidate_point] using h
  · apply Model.Instance.maximum_le _ hz
    intro j
    have h := hOffers (candidateEnumeration (Sum.inr (k,j.val))) (poisson_candidate_present v k j)
    simpa only [codeValue,poisson_candidate_point] using h

theorem maximum_attained_of_locallyFinite (B : CountableInstance) (v : CompleteWorld Seed)
    (hUpper : ∀ i, codePresent v i → codeValue v i≤B.maximum (v.1,v.2.1))
    (hFinite : ∀ b : ℝ, (B.terminal : ℝ)<b → {i : ℕ | codePresent v i ∧ b<codeValue v i}.Finite)
    (hM : (B.terminal : ℝ)<B.maximum (v.1,v.2.1)) :
    ∃ i : ℕ, codePresent v i ∧ codeValue v i=B.maximum (v.1,v.2.1) := by
  let b := ((B.terminal : ℝ)+B.maximum (v.1,v.2.1))/2
  have hab : (B.terminal : ℝ)<b := by dsimp only [b]; linarith only [hM]
  have hbM : b<B.maximum (v.1,v.2.1) := by dsimp only [b]; linarith only [hM]
  have hb0 : 0≤b := B.terminal.property.trans hab.le
  have hNonempty : {i : ℕ | codePresent v i ∧ b<codeValue v i}.Nonempty := by
    by_contra hn
    have hBound : ∀ i, codePresent v i → codeValue v i≤b := by
      intro i hi
      exact le_of_not_gt (fun h => hn ⟨i,hi,h⟩)
    exact (not_le_of_gt hbM) (B.maximum_le_of_codeValues v b hab.le hb0 hBound)
  obtain ⟨i,hi,hMax⟩ := Set.exists_max_image {i : ℕ | codePresent v i ∧ b<codeValue v i}
    (codeValue v) (hFinite b hab) hNonempty
  have hAll : ∀ j, codePresent v j → codeValue v j≤codeValue v i := by
    intro j hj
    by_cases hLarge : b<codeValue v j
    · exact hMax j ⟨hj,hLarge⟩
    · exact (le_of_not_gt hLarge).trans hi.2.le
  have hMaxUpper := B.maximum_le_of_codeValues v (codeValue v i) (hab.le.trans hi.2.le) (hb0.trans hi.2.le) hAll
  exact ⟨i,hi.1,le_antisymm (hUpper i hi.1) hMaxUpper⟩

variable [MeasurableSpace Seed]

theorem maximum_attained_ae (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v : CompleteWorld Seed ∂B.completeWorldLaw ν,
      (B.terminal : ℝ)<B.maximum (v.1,v.2.1) →
        ∃ i : ℕ, codePresent v i ∧ codeValue v i=B.maximum (v.1,v.2.1) := by
  filter_upwards [B.completeWorld_locallyFinite ν,B.candidate_value_le_maximum ν] with v hFinite hUpper hM
  exact B.maximum_attained_of_locallyFinite v (fun i hi => hUpper (candidateEnumeration.symm i) hi) hFinite hM

theorem competingMaximum_attained_other_ae (B : CountableInstance) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : ℕ) :
    ∀ᵐ v : CompleteWorld Seed ∂B.completeWorldLaw ν,
      (B.terminal : ℝ)<B.competingMaximum i v →
        ∃ d : Candidate, candidatePresent v d ∧ d≠Sum.inl i ∧
          (candidatePoint v d).2=B.competingMaximum i v := by
  let hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), (0 : ℝ) ∈ Icc (0 : ℝ) B.cap :=
    Eventually.of_forall (fun _ => ⟨le_rfl,B.cap.property⟩)
  let Q := B.mapIndividual i (fun _ => (0 : ℝ)) measurable_const hSupport
  have hMP := B.mapSingleIndividualWorld_measurePreserving i (fun _ => (0 : ℝ)) measurable_const hSupport ν
  have hAttained := hMP.quasiMeasurePreserving.ae (Q.maximum_attained_ae ν)
  filter_upwards [hAttained] with v hv hM
  have hLarge : (Q.terminal : ℝ)<Q.maximum
      ((mapSingleIndividualWorld i (fun _ => (0 : ℝ)) v).1,
        (mapSingleIndividualWorld i (fun _ => (0 : ℝ)) v).2.1) := hM
  obtain ⟨j,hPresent,hValue⟩ := hv hLarge
  let d := candidateEnumeration.symm j
  have hOther : d≠Sum.inl i := by
    intro he
    have hZero : codeValue (mapSingleIndividualWorld i (fun _ => (0 : ℝ)) v) j=0 := by
      change (candidatePoint (replaceIndividualValue i (v,0)) d).2=0
      rw [he]
      simp only [candidatePoint,replaceIndividualValue,Function.update_self]
    have hMaxZero : B.competingMaximum i v=0 := hValue.symm.trans hZero
    rw [hMaxZero] at hM
    exact (not_lt_of_ge B.terminal.property) hM
  refine ⟨d,(candidatePresent_replaceIndividualValue i (v,0) d).mp hPresent,hOther,?_⟩
  have hPoint := candidatePoint_replaceIndividualValue_of_ne i (v,0) d hOther
  exact (congrArg Prod.snd hPoint).symm.trans hValue

theorem individual_no_competing_tie_of_unique_positive_maximum
    (B : CountableInstance) (hTerminal : B.terminal=0) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : ℕ)
    (hUnique : ∀ᵐ v : CompleteWorld Seed ∂B.completeWorldLaw ν,
      ∀ d e : Candidate, candidatePresent v d → candidatePresent v e →
        (candidatePoint v d).2=B.maximum (v.1,v.2.1) →
        (candidatePoint v e).2=B.maximum (v.1,v.2.1) → 0<B.maximum (v.1,v.2.1) → d=e) :
    ∀ᵐ v : CompleteWorld Seed ∂B.completeWorldLaw ν,
      0<v.2.1 i → v.2.1 i≠B.competingMaximum i v := by
  filter_upwards [B.competingMaximum_attained_other_ae ν i,B.maximum_eq_max_competing_ae ν i,hUnique]
    with v hAttained hMaximum hUniqueV hPos hTie
  have hComp : (B.terminal : ℝ)<B.competingMaximum i v := by
    simpa only [hTerminal,NNReal.coe_zero] using hPos.trans_eq hTie
  obtain ⟨d,hPresent,hOther,hValue⟩ := hAttained hComp
  have hRealized : B.maximum (v.1,v.2.1)=v.2.1 i := by rw [hMaximum,← hTie,max_self]
  have hSame := hUniqueV (Sum.inl i) d trivial hPresent hRealized.symm
    (hValue.trans (hTie.symm.trans hRealized.symm)) (hPos.trans_eq hRealized.symm)
  exact hOther hSame.symm

end ProphetSecretary.Limiting.CountableInstance
