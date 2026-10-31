import ProphetSecretary.Limiting.CountablePolicyBounds

/-!
# A common local-finiteness event for actual occurrences

Borel--Cantelli at countably many cutoffs tending to the reserve gives one
probability-one event valid at every positive distance above it. Construction
bands then give the same property for actual analytical candidate labels.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance)

lemma individualValues_locallyFinite :
    ∀ᵐ x ∂B.individualValuesLaw, ∀ b : ℝ, (B.terminal : ℝ) < b → {i : ℕ | b < x i}.Finite := by
  have hcut : ∀ᵐ x ∂B.individualValuesLaw, ∀ k : ℕ, {i : ℕ | B.markCutoff k < x i}.Finite :=
    ae_all_iff.mpr (fun k => B.ae_finite_individuals_above (B.terminal_lt_markCutoff k))
  filter_upwards [hcut] with x hx
  intro b hb
  obtain ⟨k,hk⟩ := (B.markCutoff_tendsto.eventually (gt_mem_nhds hb)).exists
  exact (hx k).subset (fun i hi => hk.trans hi)

lemma physicalCandidates_finite_of_data {Seed : Type*} (v : CompleteWorld Seed) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) (hx : {i : ℕ | b < v.2.1 i}.Finite)
    (hband : ∀ k j, ((v.1 k).2 j).2 ∈ B.markBand k) :
    {i : ℕ | codePresent v i ∧ b < codeValue v i}.Finite := by
  obtain ⟨K,hK⟩ := B.eventually_bands_below hb
  let F : Finset ℕ := (Finset.range (K+1)).biUnion (fun k =>
    (Finset.range (v.1 k).1).image (fun j => candidateEnumeration (Sum.inr (k,j))))
  have hI : (candidateEnumeration ∘ Sum.inl '' {i : ℕ | b < v.2.1 i}).Finite := hx.image _
  apply (hI.union F.finite_toSet).subset
  intro i hi
  change codePresent v i ∧ b < codeValue v i at hi
  have hencode : candidateEnumeration (candidateEnumeration.symm i) = i := Equiv.apply_symm_apply _ _
  cases hc : candidateEnumeration.symm i with
  | inl j =>
    left
    refine ⟨j,?_,?_⟩
    · change b < v.2.1 j
      simpa only [codeValue,codePoint,hc,candidatePoint] using hi.2
    · change candidateEnumeration (Sum.inl j) = i
      rw [hc] at hencode
      exact hencode
  | inr kj =>
    have hp : kj.2 < (v.1 kj.1).1 := by simpa only [codePresent,hc,candidatePresent] using hi.1
    have hvalue : codeValue v i = ((v.1 kj.1).2 ⟨kj.2,hp⟩).2 := by
      simp only [codeValue,codePoint,hc,candidatePoint,configurationPoint,dif_pos hp]
    have hle : kj.1 ≤ K := by
      by_contra hn
      have hmark := hK kj.1 (lt_of_not_ge hn) _ (hband kj.1 ⟨kj.2,hp⟩)
      rw [hvalue] at hi
      exact (not_lt_of_ge hmark) hi.2
    right
    change i ∈ F
    apply Finset.mem_biUnion.mpr
    refine ⟨kj.1,Finset.mem_range.mpr (by omega),?_⟩
    apply Finset.mem_image.mpr
    rw [hc] at hencode
    exact ⟨kj.2,Finset.mem_range.mpr hp,hencode⟩

lemma completeWorld_locallyFinite {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂B.completeWorldLaw ν, ∀ b : ℝ, (B.terminal : ℝ) < b →
      {i : ℕ | codePresent v i ∧ b < codeValue v i}.Finite := by
  have hx0 := (Measure.quasiMeasurePreserving_snd (μ := B.bandConfigurationsLaw)
    (ν := B.individualValuesLaw)).ae B.individualValues_locallyFinite
  have hx := (B.value_projection_measurePreserving ν).quasiMeasurePreserving.ae hx0
  have hp := (Measure.quasiMeasurePreserving_fst (μ := B.bandConfigurationsLaw)
    (ν := B.individualWorldLaw ν)).ae B.bandConfigurations_marks_in_band
  filter_upwards [hx,hp] with v hv hband
  intro b hb
  exact B.physicalCandidates_finite_of_data v b hb (hv b hb) hband

end ProphetSecretary.Limiting.CountableInstance
