import ProphetSecretary.Model.Continuation

/-!
# Bellman base cases

An empty state has only terminal duration payoff. With one offer, the best
possible action compares acceptance against waiting to the terminal time.
These comparisons apply to arbitrary randomized history-dependent policies.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {Seed : Type*}

lemma RandomizedPolicy.empty_scalarObjective (π : RandomizedPolicy 0) (P : Instance 0)
    (w c : ℝ) : π.scalarObjective P w c = c := by
  simp [scalarObjective, realizedReward, Policy.reward, realizedDuration,
    Policy.stoppingTime, Policy.stopTimes, Policy.accepted]

lemma optimalScalarValue_empty (P : Instance 0) (w c : ℝ) : optimalScalarValue P w c = c := by
  have hs : {v | ∃ π : RandomizedPolicy 0, v = π.scalarObjective P w c} = {c} := by
    ext v
    constructor
    · rintro ⟨π, rfl⟩
      simp only [π.empty_scalarObjective P w c, mem_singleton_iff]
    · intro hv
      exact ⟨RandomizedPolicy.waiting 0, (mem_singleton_iff.mp hv).trans
        (RandomizedPolicy.waiting_scalarObjective P w c).symm⟩
  unfold optimalScalarValue
  rw [hs]
  simp

lemma Instance.continuationValue_empty {n : ℕ} (P : Instance n) (u w c : ℝ) :
    P.continuationValue ∅ u w c = c * u :=
  optimalScalarValue_empty (P.restrictTo ∅) w (c * u)

/-- With reward coefficient zero, waiting is optimal on every finite instance,
without any reward integrability assumption. -/
lemma optimalScalarValue_zero_rewardWeight {n : ℕ} (P : Instance n) {c : ℝ} (hc : 0 ≤ c) :
    optimalScalarValue P 0 c = c := by
  have hbound (π : RandomizedPolicy n) : π.scalarObjective P 0 c ≤ c := by
    have heq : π.scalarObjective P 0 c = c * π.expectedDuration P := by
      simp only [RandomizedPolicy.scalarObjective, zero_mul, zero_add, integral_const_mul]
      rfl
    rw [heq]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (π.expectedDuration_le_one P) hc
  have hb : BddAbove {v | ∃ π : RandomizedPolicy n, v = π.scalarObjective P 0 c} := by
    refine ⟨c, ?_⟩
    rintro v ⟨π, rfl⟩
    exact hbound π
  apply le_antisymm
  · exact csSup_le (scalarValues_nonempty P 0 c) (by rintro v ⟨π, rfl⟩; exact hbound π)
  · have h := le_csSup hb (show (RandomizedPolicy.waiting n).scalarObjective P 0 c ∈
        {v | ∃ π : RandomizedPolicy n, v = π.scalarObjective P 0 c} from ⟨_, rfl⟩)
    simpa only [RandomizedPolicy.waiting_scalarObjective, optimalScalarValue] using h

/-- A candidate's value and clock have their independent marginal product law,
also when arbitrary auxiliary policy randomness is present. -/
lemma Instance.world_candidate_measurePreserving {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    MeasurePreserving (fun ω : World n Seed ↦ (ω.1 i, ω.2.1 i))
      (P.worldLaw ν) ((P.law i).prod Instance.uniformClock) := by
  have hdrop := (MeasurePreserving.id P.valuesLaw).prod
    (measurePreserving_fst (μ := Instance.clocksLaw n) (ν := ν))
  exact ((measurePreserving_eval P.law i).prod
    (measurePreserving_eval (fun _ : Fin n ↦ Instance.uniformClock) i)).comp hdrop

/-- In a one-offer instance, accepting at its arrival or waiting are the only
possible outcomes, even for a randomized history-dependent rule. -/
lemma Policy.oneOffer_payoff (π : Policy Seed 1) (r : Seed) (x u : Fin 1 → ℝ)
    (hu : u 0 ≤ 1) (w c : ℝ) :
    w * π.reward r Finset.univ x u + c * π.stoppingTime r Finset.univ x u =
      if π.action r Finset.univ x u 0 = true then w * x 0 + c * u 0 else c := by
  by_cases ha : π.action r Finset.univ x u 0 = true
  · have hacc : (0 : Fin 1) ∈ π.accepted r Finset.univ x u :=
      (π.mem_accepted r Finset.univ x u 0).mpr ⟨Finset.mem_univ _, ha⟩
    have htime : π.stoppingTime r Finset.univ x u = u 0 := by
      apply le_antisymm (π.stoppingTime_le_of_accepted _ _ _ _ _ hacc)
      apply (π.le_stoppingTime_iff _ _ _ _ _).mpr
      refine ⟨hu, ?_⟩
      intro j _hj
      have hj : j = 0 := Subsingleton.elim _ _
      simpa only [hj] using (le_rfl : u 0 ≤ u 0)
    have hs : π.ActualSelects r Finset.univ x u 0 :=
      ⟨⟨hacc, htime.symm⟩, fun j _hj ↦ Fin.zero_le j⟩
    rw [if_pos ha, π.reward_eq_of_actualSelects _ _ _ _ hs, htime]
  · have hno : ∀ j, ¬π.Selects r Finset.univ x u j := by
      intro j hj
      have hj0 : j = 0 := Subsingleton.elim _ _
      subst j
      exact ha ((π.mem_accepted r Finset.univ x u 0).mp hj.1).2
    rw [if_neg ha, π.reward_eq_zero_of_no_selection _ _ _ _ hno,
      π.stoppingTime_eq_one_of_no_selection _ _ _ _ hno]
    ring

lemma Policy.oneOffer_payoff_le (π : Policy Seed 1) (r : Seed) (x u : Fin 1 → ℝ)
    (hu : u 0 ≤ 1) (w c : ℝ) :
    w * π.reward r Finset.univ x u + c * π.stoppingTime r Finset.univ x u ≤
      max c (w * x 0 + c * u 0) := by
  rw [π.oneOffer_payoff r x u hu w c]
  split_ifs
  · exact le_max_right _ _
  · exact le_max_left _ _

namespace Instance

/-- The two available one-offer action payoffs, before averaging. -/
def oneOfferEnvelope (w c : ℝ) (z : ℝ × ℝ) : ℝ := max c (w * z.1 + c * z.2)

lemma integrable_oneOfferEnvelope (P : Instance 1)
    (hP : Integrable maximum P.valuesLaw) (w c : ℝ) :
    Integrable (oneOfferEnvelope w c) ((P.law 0).prod uniformClock) := by
  have hx := (measurePreserving_fst (μ := P.law 0) (ν := uniformClock)).integrable_comp_of_integrable
    ((P.integrable_maximum_iff.mp hP) 0)
  have hu : Integrable (id : ℝ → ℝ) uniformClock :=
    ProphetSecretary.Reach.integrable_of_ae_unit _ aestronglyMeasurable_id (ae_restrict_mem measurableSet_Icc)
  have ht := (measurePreserving_snd (μ := P.law 0) (ν := uniformClock)).integrable_comp_of_integrable hu
  exact (integrable_const c).sup ((hx.const_mul w).add (ht.const_mul c))

lemma oneOfferEnvelope_measurable (w c : ℝ) : Measurable (oneOfferEnvelope w c) :=
  measurable_const.max ((measurable_const.mul measurable_fst).add
    (measurable_const.mul measurable_snd))

/-- All unseen sets in a one-offer state become empty after removing the candidate. -/
lemma oneOffer_erase (A : Finset (Fin 1)) : A.erase 0 = ∅ := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  simp [hi]

lemma valueThreshold_oneOffer (P : Instance 1) (w c : ℝ) (A : Finset (Fin 1))
    {t : ℝ} (ht : t ≤ 1) : P.valueThreshold w c A t 0 = c * (1 - t) / w := by
  unfold valueThreshold
  rw [oneOffer_erase, P.continuationValue_empty, max_eq_right (sub_nonneg.mpr ht)]

/-- Bundle the measurable value-threshold rule as a deterministic randomized
policy. Its optimality is established below only for the one-offer base case. -/
noncomputable def valuePolicy {n : ℕ} (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    RandomizedPolicy n where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := thresholdPolicy (fun (_ : Unit) A t i ↦ P.valueThreshold w c A t i)
  measurable_rule := P.valueThreshold_policy_isMeasurable hP hw hc

lemma valuePolicy_oneOffer_payoff (P : Instance 1)
    (hP : Integrable maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (x u : Fin 1 → ℝ) (hu : u 0 ≤ 1) :
    let π := (P.valuePolicy hP hw.le hc).rule
    w * π.reward () Finset.univ x u + c * π.stoppingTime () Finset.univ x u =
      oneOfferEnvelope w c (x 0, u 0) := by
  let π : Policy Unit 1 := thresholdPolicy (fun (_ : Unit) A t i ↦ P.valueThreshold w c A t i)
  change w * π.reward () Finset.univ x u + c * π.stoppingTime () Finset.univ x u = _
  have hact : π.action () Finset.univ x u 0 = true ↔ c ≤ w * x 0 + c * u 0 := by
    change decide (P.valueThreshold w c _ (u 0) 0 ≤ x 0) = true ↔ _
    rw [P.valueThreshold_oneOffer w c _ hu, decide_eq_true_eq, div_le_iff₀ hw]
    constructor <;> intro h <;> nlinarith
  rw [π.oneOffer_payoff () x u hu w c]
  by_cases h : c ≤ w * x 0 + c * u 0
  · rw [if_pos (hact.mpr h), oneOfferEnvelope, max_eq_right h]
  · rw [if_neg (fun ha ↦ h (hact.mp ha)), oneOfferEnvelope, max_eq_left (le_of_not_ge h)]

/-- Every one-offer policy is bounded by the pointwise best action, averaged
under the offer's actual law and its independent uniform clock. -/
lemma scalarObjective_oneOffer_le_envelope (P : Instance 1)
    (hP : Integrable maximum P.valuesLaw) (π : RandomizedPolicy 1) (w c : ℝ) :
    π.scalarObjective P w c ≤ ∫ z, oneOfferEnvelope w c z ∂(P.law 0).prod uniformClock := by
  have hp := P.world_candidate_measurePreserving π.seedLaw 0
  have hEnv := hp.integrable_comp_of_integrable (P.integrable_oneOfferEnvelope hP w c)
  have hInt := ((π.integrable_realizedReward P hP).const_mul w).add
    ((π.integrable_realizedDuration P).const_mul c)
  have hbound := integral_mono_ae hInt hEnv ?_
  · have he := integral_map (μ := P.worldLaw π.seedLaw) hp.measurable.aemeasurable
      (oneOfferEnvelope_measurable w c).aestronglyMeasurable
    rw [hp.map_eq] at he
    exact hbound.trans_eq he.symm
  · filter_upwards [P.world_clocks_mem_unitInterval π.seedLaw] with ω hω
    exact π.rule.oneOffer_payoff_le ω.2.2 ω.1 ω.2.1 (hω 0).2 w c

lemma valuePolicy_oneOffer_scalarObjective (P : Instance 1)
    (hP : Integrable maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (P.valuePolicy hP hw.le hc).scalarObjective P w c =
      ∫ z, oneOfferEnvelope w c z ∂(P.law 0).prod uniformClock := by
  have hp := P.world_candidate_measurePreserving (Measure.dirac ()) 0
  have he := integral_map (μ := P.worldLaw (Measure.dirac ())) hp.measurable.aemeasurable
    (oneOfferEnvelope_measurable w c).aestronglyMeasurable
  rw [hp.map_eq] at he
  refine Eq.trans ?_ he.symm
  change (∫ ω : World 1 Unit,
    w * (P.valuePolicy hP hw.le hc).rule.reward ω.2.2 Finset.univ ω.1 ω.2.1 +
      c * (P.valuePolicy hP hw.le hc).rule.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
    ∂P.worldLaw (Measure.dirac ())) = _
  apply integral_congr_ae
  filter_upwards [P.world_clocks_mem_unitInterval (Measure.dirac ())] with ω hω
  have hseed : ω.2.2 = () := Subsingleton.elim _ _
  rw [hseed]
  exact P.valuePolicy_oneOffer_payoff hP hw hc ω.1 ω.2.1 (hω 0).2

/-- Existence and exact optimality of the canonical threshold in the one-offer
base case, against the full randomized history-dependent policy class. -/
theorem valuePolicy_oneOffer_optimal (P : Instance 1)
    (hP : Integrable maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (P.valuePolicy hP hw.le hc).scalarObjective P w c = optimalScalarValue P w c := by
  apply le_antisymm (scalarObjective_le_optimal _ P hP hw.le hc)
  apply csSup_le (scalarValues_nonempty P w c)
  rintro v ⟨π, rfl⟩
  rw [P.valuePolicy_oneOffer_scalarObjective hP hw hc]
  exact P.scalarObjective_oneOffer_le_envelope hP π w c

lemma optimalScalarValue_oneOffer_envelope (P : Instance 1)
    (hP : Integrable maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue P w c = ∫ z, oneOfferEnvelope w c z ∂(P.law 0).prod uniformClock := by
  by_cases hw0 : w = 0
  · subst w
    rw [optimalScalarValue_zero_rewardWeight P hc]
    symm
    have ht : ∀ᵐ z : ℝ × ℝ ∂(P.law 0).prod uniformClock, z.2 ∈ Icc (0 : ℝ) 1 :=
      (Measure.quasiMeasurePreserving_snd (μ := P.law 0) (ν := uniformClock)).ae
        (ae_restrict_mem measurableSet_Icc)
    have heq : oneOfferEnvelope 0 c =ᵐ[(P.law 0).prod uniformClock] fun _ ↦ c := by
      filter_upwards [ht] with z hz
      dsimp [oneOfferEnvelope]
      rw [zero_mul, zero_add, max_eq_left]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2 hc
    rw [integral_congr_ae heq]
    simp
  · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    rw [← P.valuePolicy_oneOffer_optimal hP hwpos hc, P.valuePolicy_oneOffer_scalarObjective hP hwpos hc]

/-- The excess acceptance payoff over waiting; `max 0` is the positive part. -/
def oneOfferPremium (w c : ℝ) (z : ℝ × ℝ) : ℝ := max 0 (w * z.1 - c * (1 - z.2))

lemma oneOfferEnvelope_eq_premium (w c : ℝ) (z : ℝ × ℝ) :
    oneOfferEnvelope w c z = c + oneOfferPremium w c z := by
  unfold oneOfferEnvelope oneOfferPremium
  by_cases h : 0 ≤ w * z.1 - c * (1 - z.2)
  · rw [max_eq_right h, max_eq_right (by linarith : c ≤ w * z.1 + c * z.2)]
    ring
  · rw [max_eq_left (le_of_not_ge h), max_eq_left (by linarith : w * z.1 + c * z.2 ≤ c)]
    ring

lemma integrable_oneOfferPremium (P : Instance 1)
    (hP : Integrable maximum P.valuesLaw) (w c : ℝ) :
    Integrable (oneOfferPremium w c) ((P.law 0).prod uniformClock) := by
  apply ((P.integrable_oneOfferEnvelope hP w c).sub (integrable_const c)).congr
  filter_upwards [] with z
  simp only [Pi.sub_apply]
  rw [oneOfferEnvelope_eq_premium]
  ring

/-- The exact one-offer Bellman value, with all expectation and integrability
obligations discharged. The offer and clock are independent. -/
theorem optimalScalarValue_oneOffer (P : Instance 1)
    (hP : Integrable maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue P w c = c + ∫ z, oneOfferPremium w c z ∂(P.law 0).prod uniformClock := by
  rw [P.optimalScalarValue_oneOffer_envelope hP hw hc]
  simp_rw [oneOfferEnvelope_eq_premium]
  rw [integral_add (integrable_const c) (P.integrable_oneOfferPremium hP w c)]
  simp

end Instance
end ProphetSecretary.Model
