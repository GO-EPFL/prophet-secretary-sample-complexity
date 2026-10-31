import ProphetSecretary.Stability.TerminalWindow
import ProphetSecretary.Model.Independence

/-!
# Unconditional terminal-window events

The failure event tests every online offer, including arrivals after a policy
has stopped. Its product law is used without conditioning on policy survival.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Instance.world_pairs_measurePreserving (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    MeasurePreserving (fun ω : World n Seed => fun i => (ω.1 i, ω.2.1 i))
      (P.worldLaw ν) (Measure.pi (fun i => (P.law i).prod Instance.uniformClock)) := by
  have hs := (measurePreserving_prodAssoc P.valuesLaw (Instance.clocksLaw n) ν).symm
    MeasurableEquiv.prodAssoc
  have hp := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) P.law
    (fun _ => Instance.uniformClock)).symm (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
  exact measurePreserving_fst.comp ((hp.prod (MeasurePreserving.id ν)).comp hs)

def lateExceedance (x u : Fin n → ℝ) (s ℓ : ℝ) : Prop := ∃ i, s ≤ u i ∧ ℓ < x i

lemma measurableSet_lateExceedance (s ℓ : ℝ) :
    MeasurableSet {ω : World n Seed | lateExceedance ω.1 ω.2.1 s ℓ} := by
  unfold lateExceedance
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  exact (measurableSet_le measurable_const ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))).inter
    (measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_fst))

lemma Instance.lateExceedance_probability_le (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ℓ : ℝ) :
    (P.worldLaw ν).real {ω : World n Seed | lateExceedance ω.1 ω.2.1 (1-η) ℓ}
      ≤ η * P.tailCount ℓ := by
  let E : Fin n → Set (World n Seed) := fun i => {ω | 1-η ≤ ω.2.1 i ∧ ℓ < ω.1 i}
  have he : {ω : World n Seed | lateExceedance ω.1 ω.2.1 (1-η) ℓ} = ⋃ i, E i := by
    ext ω
    simp [lateExceedance,E]
  rw [he]
  have h := measure_iUnion_le E (μ := P.worldLaw ν)
  simp only [tsum_fintype] at h
  have hf : (∑ i, (P.worldLaw ν) (E i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i _ => measure_ne_top _ _)
  have hreal := ENNReal.toReal_mono hf h
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)] at hreal
  change (P.worldLaw ν).real (⋃ i, E i) ≤ _ at hreal
  calc
    _ ≤ ∑ i, (P.worldLaw ν).real (E i) := hreal
    _ = η * P.tailCount ℓ := by
      simp only [E,P.world_lateTail_probability ν _ hη0 hη1 ℓ]
      rw [← Finset.mul_sum]
      rfl

lemma Instance.noLateExceedance_probability (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ℓ : ℝ) :
    (P.worldLaw ν).real {ω : World n Seed | ¬lateExceedance ω.1 ω.2.1 (1-η) ℓ}
      = ∏ i, (1-η*(P.law i).real (Ioi ℓ)) := by
  let T : Set (ℝ × ℝ) := Ioi ℓ ×ˢ Ici (1-η)
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Ici
  have hp := P.world_pairs_measurePreserving ν
  have he : {ω : World n Seed | ¬lateExceedance ω.1 ω.2.1 (1-η) ℓ} =
      (fun ω : World n Seed => fun i => (ω.1 i,ω.2.1 i)) ⁻¹' Set.univ.pi (fun _ => Tᶜ) := by
    ext ω
    simp [lateExceedance,T,and_comm]
  rw [he,← map_measureReal_apply hp.measurable (MeasurableSet.univ_pi (fun _ => hT.compl)),
    hp.map_eq]
  change (Measure.pi (fun i => (P.law i).prod Instance.uniformClock)
    (Set.univ.pi (fun _ => Tᶜ))).toReal = _
  rw [Measure.pi_pi,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [← measureReal_def,measureReal_compl hT,probReal_univ]
  change 1-((P.law i).prod Instance.uniformClock).real (Ioi ℓ ×ˢ Ici (1-η)) = _
  rw [measureReal_prod_prod,Instance.uniformClock_probability_ge (by linarith) (by linarith)]
  ring

lemma Instance.noLateExceedance_probability_le_exp (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ℓ : ℝ) :
    (P.worldLaw ν).real {ω : World n Seed | ¬lateExceedance ω.1 ω.2.1 (1-η) ℓ}
      ≤ Real.exp (-η * P.tailCount ℓ) := by
  rw [P.noLateExceedance_probability ν hη0 hη1 ℓ]
  calc
    _ ≤ ∏ i : Fin n, Real.exp (-η*(P.law i).real (Ioi ℓ)) := by
      apply Finset.prod_le_prod
      · intro i _
        have hp : (P.law i).real (Ioi ℓ) ≤ 1 := measureReal_le_one
        have hn : 0 ≤ (P.law i).real (Ioi ℓ) := measureReal_nonneg
        nlinarith
      · intro i _
        have he := Real.add_one_le_exp (-η*(P.law i).real (Ioi ℓ))
        linarith
    _ = _ := by
      rw [← Real.exp_sum,← Finset.mul_sum]
      rfl

end ProphetSecretary.Model
