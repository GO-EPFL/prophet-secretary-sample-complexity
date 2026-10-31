import ProphetSecretary.Limiting.CountableReach

/-!
# Individual reach is independent of the candidate value

Erasing only the candidate value preserves its actual clock and every other
observation. Actual infinite-product independence is transported to the pair
of pending time and candidate clock. Exact prefix agreement then factors
reached value-set probabilities under the full countable policy class.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

def eraseIndividualValue (i : ℕ) (v : CompleteWorld Seed) : CompleteWorld Seed :=
  (v.1,(Function.update v.2.1 i 0,(v.2.2.1,v.2.2.2)))

lemma keepIndividualPending_erase_value (i : ℕ) (v : CompleteWorld Seed) :
    keepIndividualPending i (eraseIndividualValue i v)=keepIndividualPending i v := by
  unfold keepIndividualPending pendingIndividualWorld eraseIndividualValue
  rw [Function.update_idem]

variable [MeasurableSpace Seed]

lemma measurable_eraseIndividualValue (i : ℕ) : Measurable (eraseIndividualValue (Seed := Seed) i) :=
  measurable_fst.prodMk
    (((Model.measurable_eraseCoordinate i (0 : ℝ)).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))

lemma eraseIndividualValue_independent (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    IndepFun (eraseIndividualValue i) (fun v : CompleteWorld Seed => v.2.1 i) (B.completeWorldLaw ν) := by
  have hX := ProphetSecretary.Probability.infinite_erasure_independent
    (fun j => (B.individuals j : Measure ℝ)) i (0 : ℝ)
  have hI := Model.indepFun_with_seed (Model.measurable_eraseCoordinate i (0 : ℝ))
    (measurable_pi_apply i) hX (ν := individualClocksLaw.prod ν)
  have hIm : Measurable (fun z : (ℕ → ℝ) × ((ℕ → ℝ) × Seed) => (Function.update z.1 i 0,z.2)) :=
    ((Model.measurable_eraseCoordinate i (0 : ℝ)).comp measurable_fst).prodMk measurable_snd
  have hXm : Measurable (fun z : (ℕ → ℝ) × ((ℕ → ℝ) × Seed) => z.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hRaw := Model.indepFun_with_seed hIm hXm hI (ν := B.bandConfigurationsLaw)
  have hSwap := Measure.measurePreserving_swap (μ := B.bandConfigurationsLaw) (ν := B.individualWorldLaw ν)
  have hL : Measurable (fun z : ((ℕ → ℝ) × ((ℕ → ℝ) × Seed)) × BandConfigurations =>
      ((Function.update z.1.1 i 0,z.1.2),z.2)) := (hIm.comp measurable_fst).prodMk measurable_snd
  have hR := hXm.comp (measurable_fst : Measurable
    (fun z : ((ℕ → ℝ) × ((ℕ → ℝ) × Seed)) × BandConfigurations => z.1))
  exact (Model.indepFun_pullback hSwap hL hR hRaw).comp measurable_swap measurable_id

lemma CountableRule.pending_clock_value_independent (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    IndepFun (fun v : CompleteWorld Seed => (π.pendingIndividualTime i v,v.2.2.1 i))
      (fun v => v.2.1 i) (B.completeWorldLaw ν) := by
  have hF : Measurable (fun v : CompleteWorld Seed => (π.pendingIndividualTime i v,v.2.2.1 i)) :=
    (π.measurable_pendingIndividualTime hπ i).prodMk
      ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have h := (eraseIndividualValue_independent B ν i).comp hF measurable_id
  have hEq : (fun v : CompleteWorld Seed => (π.pendingIndividualTime i (eraseIndividualValue i v),
      (eraseIndividualValue i v).2.2.1 i))=(fun v => (π.pendingIndividualTime i v,v.2.2.1 i)) := by
    funext v
    unfold CountableRule.pendingIndividualTime
    rw [keepIndividualPending_erase_value]
    rfl
  change IndepFun (fun v : CompleteWorld Seed => (π.pendingIndividualTime i (eraseIndividualValue i v),
    (eraseIndividualValue i v).2.2.1 i)) (fun v => v.2.1 i) (B.completeWorldLaw ν) at h
  rw [hEq] at h
  exact h

lemma CountableRule.reach_event_eq_pending_ae (π : CountableRule Seed) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (hAdm : π.Admissible B ν) (i : ℕ) :
    {v : CompleteWorld Seed | v.2.2.1 i ≤ π.realizedDuration v} =ᵐ[B.completeWorldLaw ν]
      {v | v.2.2.1 i ≤ π.pendingIndividualTime i v} := by
  have hClock := individualClock_completeWorld_measurePreserving B ν i
  have hUnit : ∀ᵐ v ∂B.completeWorldLaw ν, v.2.2.1 i ∈ Icc (0 : ℝ) 1 :=
    hClock.quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hUnit,π.infimumDuration_eq_actual B ν hAdm] with v hv hRaw
  apply propext
  change v.2.2.1 i ≤ π.realizedDuration v ↔ v.2.2.1 i ≤ π.pendingIndividualTime i v
  rw [← hRaw]
  exact (π.le_pending_iff_le_infimum_before i v le_rfl hv.2).symm

theorem CountableRule.reach_value_probability (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (hAdm : π.Admissible B ν)
    (i : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    (B.completeWorldLaw ν).real {v | v.2.2.1 i ≤ π.realizedDuration v ∧ v.2.1 i ∈ S}=
      π.individualReachProbability B ν i*(B.individuals i : Measure ℝ).real S := by
  let μ := B.completeWorldLaw ν
  have hE := π.reach_event_eq_pending_ae B ν hAdm i
  have hConj : {v : CompleteWorld Seed | v.2.2.1 i ≤ π.realizedDuration v ∧ v.2.1 i ∈ S} =ᵐ[μ]
      {v | v.2.2.1 i ≤ π.pendingIndividualTime i v ∧ v.2.1 i ∈ S} := by
    filter_upwards [hE] with v hv
    change (v.2.2.1 i ≤ π.realizedDuration v ∧ v.2.1 i ∈ S)=
      (v.2.2.1 i ≤ π.pendingIndividualTime i v ∧ v.2.1 i ∈ S)
    exact congrArg (fun P : Prop => P ∧ v.2.1 i ∈ S) hv
  have hQ : μ.real {v | v.2.2.1 i ≤ π.pendingIndividualTime i v}=π.individualReachProbability B ν i :=
    (measureReal_congr hE).symm
  have hXi : MeasurePreserving (fun v : CompleteWorld Seed => v.2.1 i) μ (B.individuals i : Measure ℝ) :=
    (B.individualValue_measurePreserving i).comp (measurePreserving_fst.comp measurePreserving_snd)
  have hMass : μ.real {v : CompleteWorld Seed | v.2.1 i ∈ S}=(B.individuals i : Measure ℝ).real S :=
    congrArg ENNReal.toReal (hXi.measure_preimage hS.nullMeasurableSet)
  have h := (π.pending_clock_value_independent hπ B ν i).measure_inter_preimage_eq_mul
    {z : ℝ × ℝ | z.2 ≤ z.1} S (measurableSet_le measurable_snd measurable_fst) hS
  have hReal := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul] at hReal
  change μ.real {v : CompleteWorld Seed | v.2.2.1 i ≤ π.pendingIndividualTime i v ∧ v.2.1 i ∈ S}=
    μ.real {v | v.2.2.1 i ≤ π.pendingIndividualTime i v}*μ.real {v : CompleteWorld Seed | v.2.1 i ∈ S} at hReal
  rw [measureReal_congr hConj,hReal,hQ,hMass]

end ProphetSecretary.Limiting.CountableInstance
