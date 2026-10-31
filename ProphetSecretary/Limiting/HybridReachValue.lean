import ProphetSecretary.Limiting.HybridReach
import ProphetSecretary.Probability.JackpotCoupling

/-!
# A retained candidate's reach is independent of its value

The actual value is erased only in an analytical auxiliary world. Causal
execution proves reach invariance, and independent product laws then give
independence. Anonymous configurations and every other retained observation
remain present; the policy receives no erased-world or future information.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma HybridRule.retainedReachIndicator_value_independent (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    IndepFun (fun v : HybridWorld n Seed => if π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i then (1 : ℝ) else 0)
      (fun v => v.2.1 i) (hybridWorldLaw P μ ν) := by
  let I : HybridWorld n Seed → ℝ := fun v => if π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i then 1 else 0
  have hI : Measurable I := Measurable.ite (π.measurableSet_reachesIndividual hπ i) measurable_const measurable_const
  have hErase : Measurable (ProphetSecretary.Probability.eraseValueWorld (Seed := Seed) i) :=
    ((Model.measurable_eraseCoordinate i 0).comp measurable_fst).prodMk measurable_snd
  have hXi : Measurable (fun v : Model.World n Seed => v.1 i) := (measurable_pi_apply i).comp measurable_fst
  have hBase := Model.indepFun_with_seed hErase hXi
    (ProphetSecretary.Probability.erasedValueWorld_value_independent P ν i) (ν := configurationLaw μ)
  have hSwap := Measure.measurePreserving_swap (μ := configurationLaw μ) (ν := P.worldLaw ν)
  have hLeft : Measurable (fun z : Model.World n Seed × Configuration =>
      (ProphetSecretary.Probability.eraseValueWorld i z.1,z.2)) := (hErase.comp measurable_fst).prodMk measurable_snd
  have hRight : Measurable (fun z : Model.World n Seed × Configuration => z.1.1 i) := hXi.comp measurable_fst
  have hPull := Model.indepFun_pullback hSwap hLeft hRight hBase
  have hf : Measurable (fun z : Model.World n Seed × Configuration => I (z.2,z.1)) := hI.comp measurable_swap
  have hFinal := hPull.comp hf measurable_id
  have he : (fun v : HybridWorld n Seed => I (v.1,ProphetSecretary.Probability.eraseValueWorld i v.2)) =ᵐ[hybridWorldLaw P μ ν] I := by
    have hc := (Measure.quasiMeasurePreserving_snd (μ := configurationLaw μ) (ν := P.worldLaw ν)).ae
      (P.world_clocks_mem_unitInterval ν)
    filter_upwards [hc] with v hv
    change (if (π.asFinitePolicy v.1.1).Reaches v.2.2.2
      (combinedValues (Function.update v.2.1 i 0) v.1.2) (combinedClocks v.2.2.1 v.1.2) (i.castAdd v.1.1) then (1 : ℝ) else 0) = _
    rw [combinedValues_update_retained]
    rw [(π.asFinitePolicy v.1.1).reaches_update_value _ _ _ (i.castAdd v.1.1) 0
      (show combinedClocks v.2.2.1 v.1.2 (i.castAdd v.1.1) ≤ 1 by
        simpa only [combinedClocks,Fin.addCases_left] using (hv i).2)]
    rfl
  exact hFinal.congr he (EventuallyEq.rfl)

lemma HybridRule.reachedIndividualTailProbability_eq (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (i : Fin n) (b : ℝ) :
    (hybridWorldLaw P μ ν).real {v : HybridWorld n Seed |
      π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i ∧ b < v.2.1 i} =
      π.individualReachProbability P μ ν i*(P.law i).real (Ioi b) := by
  let I : HybridWorld n Seed → ℝ := fun v => if π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i then 1 else 0
  have h := (π.retainedReachIndicator_value_independent hπ P μ ν i).measure_inter_preimage_eq_mul
    ({1} : Set ℝ) (Ioi b) (measurableSet_singleton 1) measurableSet_Ioi
  have he : I ⁻¹' ({1} : Set ℝ) = {v | π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i} := by
    ext v
    change (if _ then (1 : ℝ) else 0) = 1 ↔ _
    split_ifs <;> simp_all
  change (hybridWorldLaw P μ ν) (I ⁻¹' {1} ∩ (fun v : HybridWorld n Seed => v.2.1 i) ⁻¹' Ioi b) =
    (hybridWorldLaw P μ ν) (I ⁻¹' {1})*(hybridWorldLaw P μ ν) ((fun v : HybridWorld n Seed => v.2.1 i) ⁻¹' Ioi b) at h
  rw [he] at h
  have hp : MeasurePreserving (fun v : HybridWorld n Seed => v.2.1 i) (hybridWorldLaw P μ ν) (P.law i) :=
    ((measurePreserving_eval P.law i).comp
      (measurePreserving_fst : MeasurePreserving (fun v : Model.World n Seed => v.1) (P.worldLaw ν) P.valuesLaw)).comp measurePreserving_snd
  rw [hp.measure_preimage measurableSet_Ioi.nullMeasurableSet] at h
  have hSet : ({v : HybridWorld n Seed | π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i} ∩
      (fun v : HybridWorld n Seed => v.2.1 i) ⁻¹' Ioi b) =
      {v | π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i ∧ b < v.2.1 i} := rfl
  rw [hSet] at h
  have ht := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_mul,Measure.real,HybridRule.individualReachProbability] using ht

end ProphetSecretary.Limiting
