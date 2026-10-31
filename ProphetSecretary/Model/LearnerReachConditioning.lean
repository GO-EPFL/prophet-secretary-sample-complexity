import ProphetSecretary.Model.LearnerConditioning

/-!
# Conditioning actual learner reach on independent training data

Reach is the ordinary executed reach event, including zero-valued identities.
Its unit indicator allows the same actual Fubini conditioning used for reward
and duration, without any threshold monotonicity assumption.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} {Seed Ω : Type*} [MeasurableSpace Seed] [MeasurableSpace Ω]

noncomputable def Policy.reachIndicator (π : Policy Seed n) (r : Seed) (x u : Fin n → ℝ) (i : Fin n) : ℝ :=
  if π.Reaches r x u i then 1 else 0

lemma Policy.measurable_reachIndicator (π : Policy Seed n) (hπ : π.IsMeasurable)
    {r : Ω → Seed} {x u : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ j, Measurable fun ω => x ω j) (hu : ∀ j, Measurable fun ω => u ω j) (i : Fin n) :
    Measurable (fun ω => π.reachIndicator (r ω) (x ω) (u ω) i) :=
  measurable_const.ite (π.measurableSet_reaches hπ hr hx hu i) measurable_const

omit [MeasurableSpace Seed] [MeasurableSpace Ω] in
lemma Policy.reachIndicator_mem_unit (π : Policy Seed n) (r : Seed) (x u : Fin n → ℝ) (i : Fin n) :
    π.reachIndicator r x u i∈Icc (0:ℝ) 1 := by unfold Policy.reachIndicator;split_ifs <;> norm_num

lemma Policy.reachProbability_eq_integral_indicator (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) (i : Fin n) :
    π.reachProbability P ν i=∫ ω : World n Seed, π.reachIndicator ω.2.2 ω.1 ω.2.1 i ∂P.worldLaw ν := by
  have hE := π.measurableSet_reaches hπ
    (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  exact (integral_indicator_one hE).symm

lemma Learner.measurable_frozenReachProbability (L : Learner n k) (P : Instance n) (i : Fin n) :
    Measurable (fun p : Reservoir n k × L.Seed =>
      (L.frozenRule p.1 p.2).reachProbability P (Measure.dirac ()) i) := by
  let T := (Reservoir n k × L.Seed) × World n Unit
  have hF := L.policy.measurable_reachIndicator L.policy_isMeasurable
    (measurable_fst : Measurable (Prod.fst : T → Reservoir n k × L.Seed))
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))) i
  have hMean := (hF.stronglyMeasurable.integral_prod_right' (ν:=P.worldLaw (Measure.dirac ()))).measurable
  convert hMean using 1
  funext p
  exact (L.frozenRule p.1 p.2).reachProbability_eq_integral_indicator (L.frozenRule_isMeasurable p.1 p.2) P (Measure.dirac ()) i

lemma Learner.integrable_frozenReachProbability (L : Learner n k) (P : Instance n)
    (D : Measure (Reservoir n k × L.Seed)) [IsProbabilityMeasure D] (i : Fin n) :
    Integrable (fun p : Reservoir n k × L.Seed => (L.frozenRule p.1 p.2).reachProbability P (Measure.dirac ()) i) D := by
  apply Integrable.of_bound (L.measurable_frozenReachProbability P i).aestronglyMeasurable 1
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs]
    unfold Policy.reachProbability
    rw [abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

lemma Policy.integrable_reachIndicator (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    Integrable (fun ω : World n Seed => π.reachIndicator ω.2.2 ω.1 ω.2.1 i) (P.worldLaw ν) := by
  have hm := π.measurable_reachIndicator hπ (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Eventually.of_forall fun ω => by
    change ‖π.reachIndicator ω.2.2 ω.1 ω.2.1 i‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (π.reachIndicator_mem_unit ω.2.2 ω.1 ω.2.1 i).1]
    exact (π.reachIndicator_mem_unit ω.2.2 ω.1 ω.2.1 i).2

theorem Learner.integral_frozenReachProbability (L : Learner n k) (P : Instance n)
    (D : Measure (Reservoir n k × L.Seed)) [IsProbabilityMeasure D] (i : Fin n) :
    (∫ p, (L.frozenRule p.1 p.2).reachProbability P (Measure.dirac ()) i ∂D)=
      L.policy.reachProbability P D i := by
  have hmap := P.seedFirstWorld_measurePreserving D
  have hInt := hmap.integrable_comp_of_integrable
    (L.policy.integrable_reachIndicator L.policy_isMeasurable P D i)
  have hm := L.policy.measurable_reachIndicator L.policy_isMeasurable
    (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hMap := integral_map (μ:=D.prod (P.worldLaw (Measure.dirac ()))) hmap.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hmap.map_eq] at hMap
  have hFub := integral_prod (fun z : (Reservoir n k × L.Seed) × World n Unit =>
    L.policy.reachIndicator z.1 z.2.1 z.2.2.1 i) hInt
  calc
    (∫ p, (L.frozenRule p.1 p.2).reachProbability P (Measure.dirac ()) i ∂D)=
        ∫ p, ∫ ω : World n Unit, L.policy.reachIndicator p ω.1 ω.2.1 i ∂P.worldLaw (Measure.dirac ()) ∂D := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p =>
        (L.frozenRule p.1 p.2).reachProbability_eq_integral_indicator (L.frozenRule_isMeasurable p.1 p.2) P (Measure.dirac ()) i
    _=∫ ω : World n (Reservoir n k × L.Seed), L.policy.reachIndicator ω.2.2 ω.1 ω.2.1 i ∂P.worldLaw D :=
      hFub.symm.trans hMap.symm
    _=L.policy.reachProbability P D i :=
      (L.policy.reachProbability_eq_integral_indicator L.policy_isMeasurable P D i).symm

end ProphetSecretary.Model
