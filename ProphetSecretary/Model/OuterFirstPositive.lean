import ProphetSecretary.Model.RewardDuration

/-!
# The zero-pilot branch: accept the first positive retained offer

Zeros remain observed identities but are rejected. Every policy's reach is
independent of that offer's own value by the already constructed erasure
argument. Combining it with the exact first-positive execution gives the
0.997 retained-maximum guarantee in `upouter:cap-pilot`.
-/

open MeasureTheory Set Filter ProbabilityTheory
open scoped Classical BigOperators
namespace ProphetSecretary
namespace Model
variable {n : ℕ} {Seed : Type*}

noncomputable def firstPositiveRule (Seed : Type*) (n : ℕ) : Policy Seed n where
  decide _ _ _ x _ := if 0<x then true else false

lemma firstPositiveRule_mem_accepted (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) :
    i∈(firstPositiveRule Seed n).accepted r D x u ↔ i∈D ∧ 0<x i := by
  by_cases hi : 0<x i <;> simp [Policy.accepted,Policy.action,firstPositiveRule,hi]

lemma firstPositiveRule_stoppingTime_eq_one (r : Seed) (x u : Fin n → ℝ) (hMax : Instance.maximum x≤0) :
    (firstPositiveRule Seed n).stoppingTime r Finset.univ x u=1 := by
  have hAcc : (firstPositiveRule Seed n).accepted r Finset.univ x u=∅ := by
    ext i
    have hi : ¬0<x i := not_lt.mpr ((Instance.le_maximum x i).trans hMax)
    simp [Policy.action,firstPositiveRule,hi]
  simp only [Policy.stoppingTime,Policy.stopTimes,hAcc,Finset.image_empty,Finset.insert_empty,Finset.min'_singleton]

lemma firstPositiveRule_reaches_of_nonpositive_maximum (r : Seed) (x u : Fin n → ℝ) (i : Fin n)
    (hMax : Instance.maximum x≤0) (hUi : u i≤1) : (firstPositiveRule Seed n).Reaches r x u i := by
  change u i≤(firstPositiveRule Seed n).stoppingTime r Finset.univ x u
  rw [firstPositiveRule_stoppingTime_eq_one r x u hMax]
  exact hUi

lemma firstPositiveRule_reward_eq_reached_sum (r : Seed) (x u : Fin n → ℝ)
    (hx : ∀ i, 0≤x i) (hu : Function.Injective u) :
    (firstPositiveRule Seed n).reward r Finset.univ x u=
      ∑ i, x i*(if (firstPositiveRule Seed n).Reaches r x u i then 1 else 0) := by
  unfold Policy.reward
  apply Finset.sum_congr rfl
  intro i _
  by_cases hpos : 0<x i
  · have hAcc := (firstPositiveRule_mem_accepted r Finset.univ x u i).mpr ⟨Finset.mem_univ _,hpos⟩
    have hSel : (firstPositiveRule Seed n).ActualSelects r Finset.univ x u i ↔
        (firstPositiveRule Seed n).Reaches r x u i := by
      rw [Policy.actualSelects_iff_selects _ _ _ _ _ hu]
      constructor
      · exact fun h => le_of_eq h.2
      · intro h
        exact ⟨hAcc,le_antisymm h ((firstPositiveRule Seed n).stoppingTime_le_of_accepted r Finset.univ x u i hAcc)⟩
    by_cases hReach : (firstPositiveRule Seed n).Reaches r x u i
    · rw [if_pos (hSel.mpr hReach),if_pos hReach,mul_one]
    · rw [if_neg (fun h => hReach (hSel.mp h)),if_neg hReach,mul_zero]
  · have hZero : x i=0 := le_antisymm (le_of_not_gt hpos) (hx i)
    simp only [hZero,ite_self,zero_mul]

variable [MeasurableSpace Seed]

lemma firstPositiveRule_isMeasurable : (firstPositiveRule Seed n).IsMeasurable := by
  let A := Seed × (ℝ × (Fin n × (ℝ × History n)))
  have hx : Measurable (fun p : A => p.2.2.2.1) := by fun_prop
  exact measurable_const.ite (measurableSet_lt measurable_const hx) measurable_const

lemma firstPositiveRule_reach_lower (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    1-P.valuesLaw.real {x | 0<Instance.maximum x}≤(firstPositiveRule Seed n).reachProbability P ν i := by
  let μ := P.worldLaw ν
  let E : Set (World n Seed) := {ω | Instance.maximum ω.1≤0}
  let R : Set (World n Seed) := {ω | (firstPositiveRule Seed n).Reaches ω.2.2 ω.1 ω.2.1 i}
  have hIncl : E≤ᵐ[μ] R := by
    filter_upwards [P.world_clocks_mem_unitInterval ν] with ω hU hE
    exact firstPositiveRule_reaches_of_nonpositive_maximum ω.2.2 ω.1 ω.2.1 i hE (hU i).2
  have hMass : μ.real E≤μ.real R := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hIncl)
  have hOrig : MeasurePreserving (fun ω : World n Seed => ω.1) μ P.valuesLaw := measurePreserving_fst
  have hE : MeasurableSet {x : Fin n → ℝ | Instance.maximum x≤0} := measurableSet_le Instance.measurable_maximum measurable_const
  have hMap := map_measureReal_apply (μ:=μ) hOrig.measurable hE
  rw [hOrig.map_eq] at hMap
  have hComp : P.valuesLaw.real {x | Instance.maximum x≤0}=1-P.valuesLaw.real {x | 0<Instance.maximum x} := by
    simpa only [Set.compl_setOf,not_lt] using probReal_compl_eq_one_sub (μ:=P.valuesLaw)
      (measurableSet_lt measurable_const Instance.measurable_maximum)
  change 1-P.valuesLaw.real {x | 0<Instance.maximum x}≤μ.real R
  rw [←hComp,hMap]
  exact hMass

end Model

namespace Model
variable {n : ℕ}

/-- Integrability and exact first-moment factorization of a reached value, for
an unrestricted admissible policy. Erasure independence is reused, not assumed. -/
lemma RandomizedPolicy.reachedValue_integrable_and_integral (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) :
    Integrable (fun ω : π.World => ω.1 i*(if π.rule.Reaches ω.2.2 ω.1 ω.2.1 i then 1 else 0)) (P.worldLaw π.seedLaw) ∧
    (∫ ω : π.World, ω.1 i*(if π.rule.Reaches ω.2.2 ω.1 ω.2.1 i then 1 else 0) ∂P.worldLaw π.seedLaw)=
      (∫ x, x ∂P.law i)*π.rule.reachProbability P π.seedLaw i := by
  let μ := P.worldLaw π.seedLaw
  let I : π.World → ℝ := fun ω => if π.rule.Reaches ω.2.2 ω.1 ω.2.1 i then 1 else 0
  have hE := π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hIm : Measurable I := measurable_const.ite hE measurable_const
  have hII : Integrable I μ := Integrable.of_bound hIm.aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by dsimp [I];split_ifs <;> norm_num)
  have hVal : MeasurePreserving (fun ω : π.World => ω.1 i) μ (P.law i) :=
    (measurePreserving_eval P.law i).comp measurePreserving_fst
  have hXI := hVal.integrable_comp_of_integrable (P.integrable_maximum_iff.mp hP i)
  have hInd := ProphetSecretary.Probability.reachIndicator_value_independent P π.seedLaw i π.rule π.measurable_rule
  refine ⟨hInd.symm.integrable_mul hXI hII,?_⟩
  have hFact := hInd.symm.integral_fun_mul_eq_mul_integral hXI.aestronglyMeasurable hII.aestronglyMeasurable
  have hValMean := integral_map (μ:=μ) hVal.measurable.aemeasurable aestronglyMeasurable_id
  rw [hVal.map_eq] at hValMean
  change (∫ x : ℝ, x ∂P.law i)=(∫ ω : π.World, ω.1 i ∂μ) at hValMean
  have hIMean : (∫ ω, I ω ∂μ)=π.rule.reachProbability P π.seedLaw i := by
    simpa only [I,μ,Policy.reachProbability,Set.indicator_apply,Pi.one_apply,Set.mem_setOf_eq,Function.comp_def] using integral_indicator_one (μ:=μ) hE
  change (∫ ω : π.World, ω.1 i*I ω ∂μ)=_
  rw [hFact,←hValMean,hIMean]

noncomputable def firstPositivePolicy (n : ℕ) : RandomizedPolicy n where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := firstPositiveRule Unit n
  measurable_rule := firstPositiveRule_isMeasurable

lemma firstPositivePolicy_expectedReward (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    (firstPositivePolicy n).expectedReward P=
      ∑ i, (∫ x, x ∂P.law i)*(firstPositivePolicy n).rule.reachProbability P (Measure.dirac ()) i := by
  let π := firstPositivePolicy n
  let μ := P.worldLaw π.seedLaw
  have hVal : MeasurePreserving (fun ω : π.World => ω.1) μ P.valuesLaw := measurePreserving_fst
  have hClock : MeasurePreserving (fun ω : π.World => ω.2.1) μ (Instance.clocksLaw n) :=
    measurePreserving_fst.comp measurePreserving_snd
  have hPoint : π.realizedReward =ᵐ[μ] (fun ω => ∑ i, ω.1 i*(if π.rule.Reaches ω.2.2 ω.1 ω.2.1 i then 1 else 0)) := by
    filter_upwards [hVal.quasiMeasurePreserving.ae P.ae_nonnegative,hClock.quasiMeasurePreserving.ae (Instance.clocks_pairwise_distinct (n:=n))] with ω hX hU
    exact firstPositiveRule_reward_eq_reached_sum ω.2.2 ω.1 ω.2.1 hX hU
  change (∫ ω, π.realizedReward ω ∂μ)=_
  rw [integral_congr_ae hPoint,integral_finsetSum _ (fun i _ => (π.reachedValue_integrable_and_integral P hP i).1)]
  exact Finset.sum_congr rfl fun i _ => (π.reachedValue_integrable_and_integral P hP i).2

/-- The B=0 branch of `upouter:cap-pilot`. -/
theorem firstPositivePolicy_reward_ge_retained_fraction (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (hRare : P.valuesLaw.real {x | 0<Instance.maximum x}≤3/1000) :
    (997/1000:ℝ)*P.expectedMaximum≤(firstPositivePolicy n).expectedReward P := by
  have hReach (i : Fin n) : (997/1000:ℝ)≤(firstPositivePolicy n).rule.reachProbability P (Measure.dirac ()) i := by
    have h := firstPositiveRule_reach_lower P (Measure.dirac ()) i
    change (997/1000:ℝ)≤(firstPositiveRule Unit n).reachProbability P (Measure.dirac ()) i
    linarith only [h,hRare]
  rw [firstPositivePolicy_expectedReward P hP]
  calc
    (997/1000:ℝ)*P.expectedMaximum≤(997/1000:ℝ)*P.totalFirstMoment :=
      mul_le_mul_of_nonneg_left (P.expectedMaximum_le_totalFirstMoment hP) (by norm_num)
    _=∑ i, (∫ x, x ∂P.law i)*(997/1000:ℝ) := by rw [Instance.totalFirstMoment,Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;ring
    _≤∑ i, (∫ x, x ∂P.law i)*(firstPositivePolicy n).rule.reachProbability P (Measure.dirac ()) i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hReach i) (integral_nonneg_of_ae (P.nonnegative i))

end Model
end ProphetSecretary
