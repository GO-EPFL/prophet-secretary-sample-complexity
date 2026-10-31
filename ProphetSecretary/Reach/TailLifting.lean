import ProphetSecretary.Model.Truncation
import ProphetSecretary.Probability.JackpotCoupling
import Mathlib.Probability.Independence.Integration

/-!
# Exact tail recovery by cap-accepting policies

A reached cap is an observation at which the policy accepts. Its original excess value
is therefore recovered by the causal value pullback. The independence used below is
derived from the executed policy's value-erasure invariance, not assumed of its reach.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

/-- Cap acceptance on one executed display path. Only arrivals actually reached are
constrained; decisions after the policy stops are irrelevant. -/
def Policy.AcceptsReachedCap (π : Policy Seed n) (H : ℝ≥0) (r : Seed)
    (x u : Fin n → ℝ) : Prop :=
  ∀ i, π.Reaches r x u i → x i = (H : ℝ) → π.action r Finset.univ x u i = true

lemma Policy.selected_iff_reached_at_cap (π : Policy Seed n) (H : ℝ≥0) (r : Seed)
    (x u : Fin n → ℝ) (hu : Function.Injective u)
    (hacc : π.AcceptsReachedCap H r x u) (i : Fin n) (hi : x i = (H : ℝ)) :
    π.ActualSelects r Finset.univ x u i ↔ π.Reaches r x u i := by
  constructor
  · intro h
    exact π.selects_implies_reaches r x u h.1
  · intro hr
    have ha : i ∈ π.accepted r Finset.univ x u :=
      (π.mem_accepted r Finset.univ x u i).mpr ⟨Finset.mem_univ i, hacc i hr hi⟩
    have htime : u i = π.stoppingTime r Finset.univ x u :=
      le_antisymm hr (π.stoppingTime_le_of_accepted r Finset.univ x u i ha)
    exact (π.actualSelects_iff_selects r Finset.univ x u hu i).mpr ⟨ha, htime⟩

/-- Exact pathwise clipping gain, including atoms at the cap. Arrival-clock ties are
excluded here and are null under the model's independent uniform clocks. -/
lemma Policy.reward_cap_pullback_eq_tail_gain (π : Policy Seed n) (H : ℝ≥0) (r : Seed)
    (x u : Fin n → ℝ) (hu : Function.Injective u)
    (hacc : π.AcceptsReachedCap H r (capValue H ∘ x) u) :
    (π.pullbackValues (capValue H)).reward r Finset.univ x u =
      π.reward r Finset.univ (capValue H ∘ x) u +
        ∑ i, if π.Reaches r (capValue H ∘ x) u i then tailValue H (x i) else 0 := by
  unfold Policy.reward
  simp only [π.pullbackValues_actualSelects_iff]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases htail : (H : ℝ) < x i
  · have hcap : (capValue H ∘ x) i = (H : ℝ) := min_eq_right htail.le
    have hs := π.selected_iff_reached_at_cap H r (capValue H ∘ x) u hu hacc i hcap
    by_cases hr : π.Reaches r (capValue H ∘ x) u i
    · have hsel := hs.mpr hr
      simp only [if_pos hr, if_pos hsel]
      exact (sub_eq_iff_eq_add.mp (sub_capValue_eq_tailValue H (x i))).trans (add_comm _ _)
    · have hsel := fun h => hr (hs.mp h)
      simp only [if_neg hr, if_neg hsel, zero_add]
  · have hcap : (capValue H ∘ x) i = x i := min_eq_left (le_of_not_gt htail)
    have he : tailValue H (x i) = 0 := max_eq_right (sub_nonpos.mpr (le_of_not_gt htail))
    simp only [hcap, he, ite_self, add_zero]

namespace Instance

lemma maximum_le_cap_add_tail (H : ℝ≥0) (x : Fin n → ℝ) :
    maximum x ≤ maximum (capValue H ∘ x) + tailFunctional H x := by
  have htail : 0 ≤ tailFunctional H x := Finset.sum_nonneg fun i _ => tailValue_nonnegative H (x i)
  apply maximum_le _ (add_nonneg (maximum_nonnegative _) htail)
  intro i
  have hcap := le_maximum (capValue H ∘ x) i
  have ht : tailValue H (x i) ≤ tailFunctional H x :=
    Finset.single_le_sum (fun j _ => tailValue_nonnegative H (x j)) (Finset.mem_univ i)
  have he := sub_capValue_eq_tailValue H (x i)
  change x i - (capValue H ∘ x) i = tailValue H (x i) at he
  linarith

/-- The prophet's clipped tail loss is at most the sum of marginal tail means. -/
lemma expectedMaximum_le_cap_add_tailSum (P : Instance n) (H : ℝ≥0)
    (hP : Integrable maximum P.valuesLaw) : P.expectedMaximum ≤ (P.cap H).expectedMaximum + P.tailSum H := by
  have hp := P.capValues_measurePreserving H
  have him := hp.integrable_comp_of_integrable (P.cap_integrable_maximum H hP)
  have hit := P.integrable_tailFunctional H hP
  have hiM : Integrable (fun x : Fin n → ℝ => maximum (capValue H ∘ x)) P.valuesLaw := him
  have h := integral_mono hP (hiM.add hit) (maximum_le_cap_add_tail H)
  change P.expectedMaximum ≤ ∫ x : Fin n → ℝ, maximum (capValue H ∘ x) + tailFunctional H x ∂P.valuesLaw at h
  rw [integral_add hiM hit, P.integral_tailFunctional H hP] at h
  have he := integral_map (μ := P.valuesLaw) hp.measurable.aemeasurable measurable_maximum.aestronglyMeasurable
  rw [hp.map_eq] at he
  rw [← he] at h
  exact h

variable [MeasurableSpace Seed]

lemma world_value_measurePreserving (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) :
    MeasurePreserving (fun ω : World n Seed => ω.1 i) (P.worldLaw ν) (P.law i) :=
  (measurePreserving_eval P.law i).comp measurePreserving_fst

lemma integrable_world_tailCoordinate (P : Instance n) (H : ℝ≥0)
    (hP : Integrable maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    Integrable (fun ω : World n Seed => tailValue H (ω.1 i)) (P.worldLaw ν) :=
  (P.world_value_measurePreserving ν i).integrable_comp_of_integrable
    (integrable_tailValue (P.law i) (P.integrable_maximum_iff.mp hP i) H)

lemma integral_world_tailCoordinate (P : Instance n) (H : ℝ≥0)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (∫ ω : World n Seed, tailValue H (ω.1 i) ∂P.worldLaw ν) = ∫ x, tailValue H x ∂P.law i := by
  have hp := P.world_value_measurePreserving ν i
  have he := integral_map (μ := P.worldLaw ν) hp.measurable.aemeasurable (measurable_tailValue H).aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm

end Instance
variable [MeasurableSpace Seed]

lemma Policy.reachProbability_cap_pullback (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (H : ℝ≥0) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (π.pullbackValues (capValue H)).reachProbability P ν i = π.reachProbability (P.cap H) ν i := by
  have hp := P.capWorld_measurePreserving H ν
  let E : Set (World n Seed) := {ω | π.Reaches ω.2.2 ω.1 ω.2.1 i}
  have hE : MeasurableSet E := π.measurableSet_reaches hπ (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  unfold Policy.reachProbability
  rw [← hp.map_eq, map_measureReal_apply hp.measurable hE]
  congr 1
  ext ω
  simp only [E, Set.mem_preimage, Set.mem_setOf_eq, Policy.Reaches, Instance.capWorld,
    π.pullbackValues_stoppingTime]

/-- Integrability and exact mean of each recovered tail. The cap is fixed; all policy
randomness, including independent training data, may be included in `ν`. -/
lemma Policy.cap_reached_tail_integral (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (H : ℝ≥0) (hP : Integrable Instance.maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    Integrable (fun ω : World n Seed => if π.Reaches ω.2.2 (capValue H ∘ ω.1) ω.2.1 i
      then tailValue H (ω.1 i) else 0) (P.worldLaw ν) ∧
    (∫ ω : World n Seed, (if π.Reaches ω.2.2 (capValue H ∘ ω.1) ω.2.1 i
      then tailValue H (ω.1 i) else 0) ∂P.worldLaw ν) =
      π.reachProbability (P.cap H) ν i * ∫ x, tailValue H x ∂P.law i := by
  let ρ := π.pullbackValues (capValue H)
  have hρ := π.pullbackValues_isMeasurable hπ (measurable_capValue H)
  let R : World n Seed → ℝ := fun ω => if ρ.Reaches ω.2.2 ω.1 ω.2.1 i then 1 else 0
  let T : World n Seed → ℝ := fun ω => tailValue H (ω.1 i)
  have hRset : MeasurableSet {ω : World n Seed | ρ.Reaches ω.2.2 ω.1 ω.2.1 i} :=
    ρ.measurableSet_reaches hρ (measurable_snd.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hRm : Measurable R := Measurable.ite hRset measurable_const measurable_const
  have hTm : Measurable T := (measurable_tailValue H).comp ((measurable_pi_apply i).comp measurable_fst)
  have hRi : Integrable R (P.worldLaw ν) := by
    apply Integrable.of_bound hRm.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω => by dsimp [R]; split_ifs <;> norm_num
  have hTi : Integrable T (P.worldLaw ν) := P.integrable_world_tailCoordinate H hP ν i
  have hi₀ := ProphetSecretary.Probability.reachIndicator_value_independent P ν i ρ hρ
  have hi : IndepFun R T (P.worldLaw ν) := hi₀.comp measurable_id (measurable_tailValue H)
  have hRT : Integrable (fun ω => R ω * T ω) (P.worldLaw ν) := hi.integrable_mul hRi hTi
  have he (ω : World n Seed) : (if π.Reaches ω.2.2 (capValue H ∘ ω.1) ω.2.1 i then tailValue H (ω.1 i) else 0) = R ω * T ω := by
    have hreach : ρ.Reaches ω.2.2 ω.1 ω.2.1 i ↔ π.Reaches ω.2.2 (capValue H ∘ ω.1) ω.2.1 i := by
      simp only [ρ, Policy.Reaches, Policy.pullbackValues_stoppingTime]
    dsimp [R, T]
    by_cases hr : π.Reaches ω.2.2 (capValue H ∘ ω.1) ω.2.1 i
    · simp only [if_pos hr, if_pos (hreach.mpr hr), one_mul]
    · simp only [if_neg hr, if_neg (fun h => hr (hreach.mp h)), zero_mul]
  constructor
  · simpa only [he] using hRT
  · simp_rw [he]
    rw [hi.integral_fun_mul_eq_mul_integral hRm.aestronglyMeasurable hTm.aestronglyMeasurable]
    have hRmean : (∫ ω, R ω ∂P.worldLaw ν) = ρ.reachProbability P ν i := by
      have h := integral_indicator_const (μ := P.worldLaw ν) (1 : ℝ) hRset
      simpa only [R, Set.indicator, Set.mem_setOf_eq, Pi.one_apply, smul_eq_mul, mul_one, Policy.reachProbability] using h
    rw [hRmean, π.reachProbability_cap_pullback hπ P H ν i, P.integral_world_tailCoordinate H ν i]

namespace RandomizedPolicy

/-- Exact clipping reward recovery. This theorem is conditional only on the stated
cap-acceptance property of the given policy; no optimality assumption is used. -/
lemma expectedReward_cap_pullback_eq_tail_gain (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (hacc : ∀ᵐ ω : π.World ∂(P.cap H).worldLaw π.seedLaw,
      π.rule.AcceptsReachedCap H ω.2.2 ω.1 ω.2.1) :
    (π.pullbackValues (capValue H) (measurable_capValue H)).expectedReward P =
      π.expectedReward (P.cap H) +
        ∑ i, π.rule.reachProbability (P.cap H) π.seedLaw i * ∫ x, tailValue H x ∂P.law i := by
  have hp := P.capWorld_measurePreserving H π.seedLaw
  let G (i : Fin n) (ω : π.World) :=
    if π.rule.Reaches ω.2.2 (capValue H ∘ ω.1) ω.2.1 i then tailValue H (ω.1 i) else 0
  have hiG (i : Fin n) : Integrable (G i) (P.worldLaw π.seedLaw) :=
    (π.rule.cap_reached_tail_integral π.measurable_rule P H hP π.seedLaw i).1
  have hiSum : Integrable (fun ω : π.World => ∑ i, G i ω) (P.worldLaw π.seedLaw) :=
    integrable_finsetSum _ (fun i _ => hiG i)
  have hiCap : Integrable (fun ω : π.World => π.realizedReward (Instance.capWorld H ω)) (P.worldLaw π.seedLaw) :=
    hp.integrable_comp_of_integrable (π.integrable_realizedReward (P.cap H) (P.cap_integrable_maximum H hP))
  have hae : ∀ᵐ ω : π.World ∂P.worldLaw π.seedLaw,
      (π.pullbackValues (capValue H) (measurable_capValue H)).realizedReward ω =
        π.realizedReward (Instance.capWorld H ω) + ∑ i, G i ω := by
    filter_upwards [hp.quasiMeasurePreserving.ae hacc, P.world_clocks_distinct π.seedLaw] with ω hω hu
    exact π.rule.reward_cap_pullback_eq_tail_gain H ω.2.2 ω.1 ω.2.1 hu hω
  have heCap := integral_map (μ := P.worldLaw π.seedLaw) hp.measurable.aemeasurable π.measurable_realizedReward.aestronglyMeasurable
  rw [hp.map_eq] at heCap
  change (∫ ω : π.World, (π.pullbackValues (capValue H) (measurable_capValue H)).realizedReward ω ∂P.worldLaw π.seedLaw) = _
  rw [integral_congr_ae hae, integral_add hiCap hiSum, integral_finsetSum _ (fun i _ => hiG i), ← heCap]
  apply congrArg (π.expectedReward (P.cap H) + ·)
  apply Finset.sum_congr rfl
  intro i _
  exact (π.rule.cap_reached_tail_integral π.measurable_rule P H hP π.seedLaw i).2

/-- The unrounded lifting conclusion: a reward guarantee and matching reach floor
on capped displays transfer to the original independent instance. -/
lemma cap_pullback_reward_guarantee (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (hacc : ∀ᵐ ω : π.World ∂(P.cap H).worldLaw π.seedLaw,
      π.rule.AcceptsReachedCap H ω.2.2 ω.1 ω.2.1)
    {rho Delta : ℝ} (hrho : 0 ≤ rho)
    (hR : rho * (P.cap H).expectedMaximum - Delta ≤ π.expectedReward (P.cap H))
    (hq : ∀ i, rho ≤ π.rule.reachProbability (P.cap H) π.seedLaw i) :
    rho * P.expectedMaximum - Delta ≤
      (π.pullbackValues (capValue H) (measurable_capValue H)).expectedReward P := by
  rw [π.expectedReward_cap_pullback_eq_tail_gain P H hP hacc]
  have htail : rho * P.tailSum H ≤
      ∑ i, π.rule.reachProbability (P.cap H) π.seedLaw i * ∫ x, tailValue H x ∂P.law i := by
    rw [Instance.tailSum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hq i) (integral_nonneg fun x => tailValue_nonnegative H x)
  have hmax := mul_le_mul_of_nonneg_left (P.expectedMaximum_le_cap_add_tailSum H hP) hrho
  nlinarith

end RandomizedPolicy

end ProphetSecretary.Model
