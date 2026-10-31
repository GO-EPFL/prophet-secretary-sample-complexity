import ProphetSecretary.Limiting.CountableCriticalPoissonAtom
import ProphetSecretary.Limiting.ConfigurationMarkAtoms

/-!
# Critical positive Poisson maxima occur only once

The intensity has countably many atoms. The critical atom-CDF result makes
the realized maximum avoid every positive one. Within a construction band,
independent marks can coincide only at such an atom; different bands have
disjoint mark supports. These are statements about actual occurrences.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal
namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def intensityAtoms (B : CountableInstance) : Set ℝ := {x | 0<B.intensity {x}}

lemma countable_intensityAtoms (B : CountableInstance) : B.intensityAtoms.Countable := by
  have h := Measure.countable_meas_level_set_pos (μ := B.intensity) measurable_id
  apply h.mono
  intro x hx
  change 0<B.intensity {y : ℝ | id y=x}
  have he : {y : ℝ | id y=x}={x} := by ext y; simp
  rw [he]
  exact hx

lemma critical_maximum_avoids_positive_atoms (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) :
    ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      ∀ x∈B.intensityAtoms, 0<x → B.maximum (v.1,v.2.1)≠x := by
  letI : Countable B.intensityAtoms := B.countable_intensityAtoms.to_subtype
  have hOne (x : B.intensityAtoms) : ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      0<(x : ℝ) → B.maximum (v.1,v.2.1)≠(x : ℝ) := by
    by_cases hx : 0<(x : ℝ)
    · have hCdf := B.critical_poisson_atom_cdf_zero hw hc hCritical x hx x.property
      have hNull : B.valueLaw {v | B.maximum v≤(x : ℝ)}=0 := by
        exact ((ENNReal.toReal_eq_zero_iff _).mp hCdf).resolve_right (measure_ne_top _ _)
      have hAvoid := (B.value_projection_measurePreserving (Measure.dirac ())).quasiMeasurePreserving.ae
        (measure_eq_zero_iff_ae_notMem.mp hNull)
      filter_upwards [hAvoid] with v hv _ he
      exact hv (le_of_eq he)
    · exact Eventually.of_forall (fun _ hp => (hx hp).elim)
  filter_upwards [ae_all_iff.mpr hOne] with v hv x hx hpos
  exact hv ⟨x,hx⟩ hpos

lemma band_equal_marks_mem_intensityAtoms (B : CountableInstance) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, ∀ k, ∀ j l : Fin (ω k).1,
      j≠l → ((ω k).2 j).2=((ω k).2 l).2 → ((ω k).2 j).2∈B.intensityAtoms := by
  apply ae_all_iff.mpr
  intro k
  have hOne : ∀ᵐ ω ∂configurationLaw (B.bandIntensity k), ∀ j l : Fin ω.1,
      j≠l → (ω.2 j).2=(ω.2 l).2 → (ω.2 j).2∈B.intensityAtoms := by
    apply configuration_equal_marks_mem (B.bandIntensity k) B.countable_intensityAtoms.measurableSet
    intro x hx
    have hZero : B.intensity {x}=0 := le_antisymm (not_lt.mp hx) bot_le
    apply le_antisymm _ bot_le
    change (B.intensity.restrict (B.markBand k)) {x}≤0
    exact (Measure.restrict_le_self _).trans_eq hZero
  exact (B.bandConfiguration_measurePreserving k).quasiMeasurePreserving.ae hOne

/-- No two different actual Poisson points attain a positive critical maximum. -/
theorem critical_poisson_maximum_unique (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) :
    ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      ∀ k l (j : Fin (v.1 k).1) (m : Fin (v.1 l).1),
      ((v.1 k).2 j).2=B.maximum (v.1,v.2.1) →
      ((v.1 l).2 m).2=B.maximum (v.1,v.2.1) →
      0<B.maximum (v.1,v.2.1) → k=l ∧ j.val=m.val := by
  have hMP : MeasurePreserving (Prod.fst : CompleteWorld Unit → BandConfigurations)
      (B.completeWorldLaw (Measure.dirac ())) B.bandConfigurationsLaw := measurePreserving_fst
  filter_upwards [hMP.quasiMeasurePreserving.ae B.bandConfigurations_marks_in_band,
    hMP.quasiMeasurePreserving.ae B.band_equal_marks_mem_intensityAtoms,
    B.critical_maximum_avoids_positive_atoms hw hc hCritical] with v hMarks hCollision hAvoid
  intro k l j m hj hm hPos
  have hEq : ((v.1 k).2 j).2=((v.1 l).2 m).2 := hj.trans hm.symm
  have hkl : k=l := by
    by_contra hn
    exact Set.disjoint_left.mp (B.markBands_disjoint hn) (hMarks k j) (hEq.symm ▸ hMarks l m)
  subst l
  refine ⟨rfl,?_⟩
  by_contra hjm
  have hNe : j≠m := fun h => hjm (congrArg Fin.val h)
  have hAtom := hCollision k j m hNe hEq
  exact hAvoid _ hAtom (hPos.trans_eq hj.symm) hj.symm

end ProphetSecretary.Limiting.CountableInstance
