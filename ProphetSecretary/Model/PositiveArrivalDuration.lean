import ProphetSecretary.Model.DurationLower
import ProphetSecretary.Probability.MinimumUniform

/-!
# The sharp duration floor from positive arrivals

A policy rejecting reached zero values cannot stop before the first positive
arrival. Conditional on the values, the mean of this first arrival is
`1 / (N + 1)`, with terminal time one if there are no positive values.
The reciprocal tangent inequality then replaces `N` by its expectation.
-/

open MeasureTheory Set
open scoped Classical BigOperators NNReal

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- First arrival from `D`, with terminal time one when `D` is empty. -/
noncomputable def firstArrivalClock (D : Finset (Fin n)) (u : Fin n → ℝ) : ℝ :=
  Finset.univ.inf' (by exact ⟨none, Finset.mem_univ _⟩)
    (fun j : Option (Fin n) => j.elim 1 (fun i => if i ∈ D then u i else 1))

lemma measurable_firstArrivalClock (D : Finset (Fin n)) : Measurable (firstArrivalClock D) := by
  have hm : Measurable ((Finset.univ : Finset (Option (Fin n))).inf'
      (by exact ⟨none, Finset.mem_univ _⟩)
      (fun j : Option (Fin n) => fun u : Fin n → ℝ =>
        j.elim 1 (fun i => if i ∈ D then u i else 1))) := by
    apply Finset.inf'_induction
    · intro f hf g hg
      exact hf.inf hg
    · intro j _
      cases j with
      | none => exact measurable_const
      | some i => by_cases hi : i ∈ D <;> simp [hi, measurable_pi_apply i]
  convert hm using 1
  funext u
  simp only [firstArrivalClock, Finset.inf'_apply]

lemma firstArrivalClock_le_one (D : Finset (Fin n)) (u : Fin n → ℝ) :
    firstArrivalClock D u ≤ 1 :=
  Finset.inf'_le _ (Finset.mem_univ none)

lemma firstArrivalClock_le (D : Finset (Fin n)) (u : Fin n → ℝ) {i : Fin n} (hi : i ∈ D) :
    firstArrivalClock D u ≤ u i := by
  simpa only [firstArrivalClock, Option.elim_some, if_pos hi] using
    (Finset.inf'_le (fun j : Option (Fin n) => j.elim 1 (fun i => if i ∈ D then u i else 1))
      (Finset.mem_univ (some i)))

lemma firstArrivalClock_nonnegative (D : Finset (Fin n)) (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) : 0 ≤ firstArrivalClock D u := by
  apply Finset.le_inf'
  intro j _
  cases j with
  | none => exact zero_le_one
  | some i => by_cases hi : i ∈ D <;> simp [hi, hu i]

lemma firstArrivalClock_strict_tail (D : Finset (Fin n)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (Instance.clocksLaw n).real {u | t < firstArrivalClock D u} = (1 - t) ^ D.card := by
  have hSet : {u : Fin n → ℝ | t < firstArrivalClock D u} =
      Set.univ.pi (fun i => if i ∈ D then Ioi t else Set.univ) := by
    ext u
    simp only [Set.mem_setOf_eq, firstArrivalClock, Finset.lt_inf'_iff,
      Finset.mem_univ, forall_true_left, Set.mem_pi, Set.mem_univ]
    constructor
    · intro h i
      by_cases hi : i ∈ D
      · simpa [hi] using h (some i)
      · simp [hi]
    · intro h j
      cases j with
      | none => exact ht1
      | some i =>
        by_cases hi : i ∈ D
        · simpa [hi] using h i
        · simpa [hi] using ht1
  change ((Instance.clocksLaw n) {u | t < firstArrivalClock D u}).toReal = _
  rw [hSet, Instance.clocksLaw, Measure.pi_pi, ENNReal.toReal_prod]
  have he (i : Fin n) :
      (Instance.uniformClock (if i ∈ D then Ioi t else Set.univ)).toReal =
        if i ∈ D then 1 - t else 1 := by
    by_cases hi : i ∈ D
    · simp only [if_pos hi, ProphetSecretary.Probability.uniformClock_tail ht0,
        ENNReal.toReal_ofReal (sub_nonneg.mpr ht1.le)]
    · simp [hi]
  simp_rw [he]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

lemma integral_firstArrivalClock (D : Finset (Fin n)) :
    (∫ u, firstArrivalClock D u ∂Instance.clocksLaw n) = 1 / ((D.card : ℝ) + 1) := by
  have hRange : ∀ᵐ u ∂Instance.clocksLaw n, firstArrivalClock D u ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [Instance.clocks_mem_unitInterval (n := n)] with u hu
    exact ⟨firstArrivalClock_nonnegative D u (fun i => (hu i).1), firstArrivalClock_le_one D u⟩
  rw [ProphetSecretary.Probability.integral_eq_bounded_strict_layercake
    (Instance.clocksLaw n) (measurable_firstArrivalClock D) (1 : ℝ≥0) hRange]
  change (∫ t in Ioc (0 : ℝ) 1,
    (Instance.clocksLaw n).real {u | t < firstArrivalClock D u}) = _
  have he : (fun t : ℝ => (Instance.clocksLaw n).real {u | t < firstArrivalClock D u})
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] (fun t => (1 - t) ^ D.card) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne (1 : ℝ))] with t ht hne
    exact firstArrivalClock_strict_tail D ht.1.le (lt_of_le_of_ne ht.2 hne)
  rw [integral_congr_ae he, ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [intervalIntegral.integral_comp_sub_left (f := fun t : ℝ => t ^ D.card) 1, integral_pow]
  norm_num

/-- The set of positive identities, retaining all zero identities in histories. -/
noncomputable def positiveIdentities (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0 < x i)

noncomputable def positiveIdentityCount (x : Fin n → ℝ) : ℝ :=
  (positiveIdentities x).card

lemma positiveIdentityCount_eq_sum (x : Fin n → ℝ) :
    positiveIdentityCount x = ∑ i : Fin n, if 0 < x i then (1 : ℝ) else 0 := by
  simp [positiveIdentityCount, positiveIdentities]

lemma measurable_positiveIdentityCount : Measurable (@positiveIdentityCount n) := by
  change Measurable (fun x : Fin n → ℝ => positiveIdentityCount x)
  simp_rw [positiveIdentityCount_eq_sum]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply i))
    measurable_const measurable_const

lemma positiveIdentityCount_nonnegative (x : Fin n → ℝ) : 0 ≤ positiveIdentityCount x :=
  Nat.cast_nonneg _

lemma positiveIdentityCount_le (x : Fin n → ℝ) : positiveIdentityCount x ≤ n := by
  have h : (positiveIdentities x).card ≤ n := by
    simpa only [positiveIdentities, Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.filter_subset (fun i => 0 < x i) Finset.univ)
  change ((positiveIdentities x).card : ℝ) ≤ (n : ℝ)
  exact_mod_cast h

lemma Instance.integrable_positiveIdentityCount (P : Instance n) :
    Integrable positiveIdentityCount P.valuesLaw := by
  apply Integrable.of_bound measurable_positiveIdentityCount.aestronglyMeasurable n
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (positiveIdentityCount_nonnegative x)]
      using positiveIdentityCount_le x

lemma Instance.integral_positiveIdentityCount (P : Instance n) :
    (∫ x, positiveIdentityCount x ∂P.valuesLaw) = P.positiveCount := by
  simp_rw [positiveIdentityCount_eq_sum]
  rw [integral_finsetSum]
  · change (∑ i, ∫ x, if 0 < x i then (1 : ℝ) else 0 ∂P.valuesLaw) = _
    apply Finset.sum_congr rfl
    intro i _
    have hm := measurePreserving_eval P.law i
    have hI : (∫ x, if 0 < x i then (1 : ℝ) else 0 ∂P.valuesLaw) =
        P.valuesLaw.real {x | 0 < x i} := by
      simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_setOf_eq] using
        (integral_indicator_one (μ := P.valuesLaw)
          (measurableSet_lt measurable_const (measurable_pi_apply i)))
    rw [hI]
    exact (map_measureReal_apply hm.measurable measurableSet_Ioi).symm.trans
      (by simpa only [Instance.valuesLaw, Measure.real] using
        congrArg (fun μ : Measure ℝ => μ.real (Ioi 0)) hm.map_eq)
  · intro i _
    apply Integrable.of_bound
      (Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply i))
        measurable_const measurable_const).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      change ‖if 0 < x i then (1 : ℝ) else 0‖ ≤ 1
      split_ifs <;> norm_num

/-- The supporting line of the reciprocal at a nonnegative point. -/
lemma reciprocal_one_add_tangent {x l : ℝ} (hx : 0 ≤ x) (hl : 0 ≤ l) :
    (1 + 2*l - x) / (1+l)^2 ≤ 1 / (1+x) := by
  apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith)) (by linarith)).mpr
  nlinarith [sq_nonneg (x-l)]

lemma Instance.reciprocal_positiveIdentityCount_jensen (P : Instance n) :
    1 / (1 + P.positiveCount) ≤
      ∫ x, 1 / (1 + positiveIdentityCount x) ∂P.valuesLaw := by
  have hL : 0 ≤ P.positiveCount := P.tailCount_nonnegative 0
  have hden : 0 < 1 + P.positiveCount := by linarith
  have hInv : Integrable (fun x => 1 / (1 + positiveIdentityCount x)) P.valuesLaw := by
    apply Integrable.of_bound (measurable_const.div
      (measurable_const.add measurable_positiveIdentityCount)).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      have hx0 := positiveIdentityCount_nonnegative x
      change ‖1 / (1 + positiveIdentityCount x)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (div_le_one (by positivity : (0 : ℝ) < 1 + positiveIdentityCount x)).mpr
        (by linarith [positiveIdentityCount_nonnegative x])
  have hline : Integrable (fun x => (1 + 2*P.positiveCount - positiveIdentityCount x) /
      (1+P.positiveCount)^2) P.valuesLaw :=
    ((integrable_const _).sub P.integrable_positiveIdentityCount).div_const _
  have h := integral_mono hline hInv (fun x =>
    reciprocal_one_add_tangent (positiveIdentityCount_nonnegative x) hL)
  have he : (∫ x, (1 + 2*P.positiveCount - positiveIdentityCount x) /
      (1+P.positiveCount)^2 ∂P.valuesLaw) = 1 / (1+P.positiveCount) := by
    rw [integral_div, integral_sub (integrable_const _) P.integrable_positiveIdentityCount,
      integral_const, probReal_univ, one_smul, P.integral_positiveIdentityCount]
    field_simp
    ring
  rwa [he] at h

/-- The first positive clock as a jointly measurable function of values and clocks. -/
noncomputable def positiveArrivalClock (x u : Fin n → ℝ) : ℝ :=
  firstArrivalClock (positiveIdentities x) u

lemma measurable_positiveArrivalClock :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => positiveArrivalClock z.1 z.2) := by
  have hm : Measurable ((Finset.univ : Finset (Option (Fin n))).inf'
      (by exact ⟨none, Finset.mem_univ _⟩)
      (fun j : Option (Fin n) => fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        j.elim 1 (fun i => if 0 < z.1 i then z.2 i else 1))) := by
    apply Finset.inf'_induction
    · intro f hf g hg
      exact hf.inf hg
    · intro j _
      cases j with
      | none => exact measurable_const
      | some i =>
        exact Measurable.ite (measurableSet_lt measurable_const
          ((measurable_pi_apply i).comp measurable_fst))
          ((measurable_pi_apply i).comp measurable_snd) measurable_const
  convert hm using 1
  funext z
  simp [positiveArrivalClock, firstArrivalClock, positiveIdentities, Finset.inf'_apply]

lemma integral_positiveArrivalClock (x : Fin n → ℝ) :
    (∫ u, positiveArrivalClock x u ∂Instance.clocksLaw n) =
      1 / (1 + positiveIdentityCount x) := by
  simpa only [positiveArrivalClock, positiveIdentityCount, add_comm] using
    integral_firstArrivalClock (positiveIdentities x)

variable {Seed : Type*} [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in
lemma Policy.positiveArrivalClock_le_stoppingTime (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hz : π.RejectsReachedZero r x u) :
    positiveArrivalClock x u ≤ π.stoppingTime r Finset.univ x u := by
  apply π.le_stoppingTime_of_no_positiveArrival r x u hx hz (firstArrivalClock_le_one _ _)
  intro i hi
  have hmem : i ∈ positiveIdentities x := by simp [positiveIdentities, hi.1]
  exact not_lt_of_ge (firstArrivalClock_le (positiveIdentities x) u hmem) hi.2

lemma Instance.integrable_worldPositiveArrivalClock (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    Integrable (fun ω : World n Seed => positiveArrivalClock ω.1 ω.2.1) (P.worldLaw ν) := by
  apply Integrable.of_bound
    (measurable_positiveArrivalClock.comp (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd))).aestronglyMeasurable 1
  filter_upwards [P.world_clocks_mem_unitInterval ν] with ω hu
  change ‖positiveArrivalClock ω.1 ω.2.1‖ ≤ 1
  rw [Real.norm_eq_abs]
  change |firstArrivalClock (positiveIdentities ω.1) ω.2.1| ≤ 1
  rw [abs_of_nonneg (firstArrivalClock_nonnegative _ _ (fun i => (hu i).1))]
  exact firstArrivalClock_le_one _ _

lemma Instance.integral_worldPositiveArrivalClock (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    (∫ ω : World n Seed, positiveArrivalClock ω.1 ω.2.1 ∂P.worldLaw ν) =
      ∫ x, 1 / (1 + positiveIdentityCount x) ∂P.valuesLaw := by
  rw [Instance.worldLaw, integral_prod _ (P.integrable_worldPositiveArrivalClock ν)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (∫ q : (Fin n → ℝ) × Seed, positiveArrivalClock x q.1
      ∂(Instance.clocksLaw n).prod ν) = 1 / (1 + positiveIdentityCount x)
    rw [integral_fun_fst, probReal_univ, one_smul, integral_positiveArrivalClock]

/-- The sharp dimension-free duration floor for every zero-rejecting policy. -/
theorem Policy.meanDuration_ge_reciprocal_positiveCount (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hz : ∀ᵐ ω : World n Seed ∂P.worldLaw ν,
      π.RejectsReachedZero ω.2.2 ω.1 ω.2.1) :
    1 / (1 + P.positiveCount) ≤ π.meanDuration P ν := by
  have hvals : ∀ᵐ ω : World n Seed ∂P.worldLaw ν, ∀ i, 0 ≤ ω.1 i :=
    (measurePreserving_fst : MeasurePreserving (fun ω : World n Seed => ω.1)
      (P.worldLaw ν) P.valuesLaw).quasiMeasurePreserving.ae P.ae_nonnegative
  have h := integral_mono_ae (P.integrable_worldPositiveArrivalClock ν)
    (P.integrable_worldTime ν π hπ Finset.univ) (by
      filter_upwards [hvals, hz] with ω hx hzero
      exact π.positiveArrivalClock_le_stoppingTime ω.2.2 ω.1 ω.2.1 hx hzero)
  rw [P.integral_worldPositiveArrivalClock ν] at h
  exact P.reciprocal_positiveIdentityCount_jensen.trans h

lemma RandomizedPolicy.expectedDuration_ge_reciprocal_positiveCount (π : RandomizedPolicy n)
    (P : Instance n)
    (hz : ∀ᵐ ω : π.World ∂P.worldLaw π.seedLaw,
      π.rule.RejectsReachedZero ω.2.2 ω.1 ω.2.1) :
    1 / (1 + P.positiveCount) ≤ π.expectedDuration P :=
  π.rule.meanDuration_ge_reciprocal_positiveCount π.measurable_rule P π.seedLaw hz

lemma Instance.valuePolicy_duration_ge_reciprocal_positiveCount (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (Q : Instance n) :
    1 / (1 + Q.positiveCount) ≤ (P.valuePolicy hP hw.le hc.le).expectedDuration Q := by
  apply RandomizedPolicy.expectedDuration_ge_reciprocal_positiveCount
  exact Filter.Eventually.of_forall fun ω =>
    P.valuePolicy_rejectsReachedZero hP hw hc ω.2.2 ω.1 ω.2.1

end ProphetSecretary.Model
