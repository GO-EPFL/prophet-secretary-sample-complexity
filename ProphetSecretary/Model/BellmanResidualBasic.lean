import ProphetSecretary.Model.BellmanPerformance
import ProphetSecretary.Model.ContinuationODE

/-!
# Fixed-design Bellman residuals

The design law `Q` supplies continuation values; the independent online offers have
true law `P`. Their transition discrepancy uses the positive part of acceptance minus
continuation. It is a signed quantity, distinct from the nonnegative action loss.
Design continuation at an arrival depends only on clocks and unseen identities.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

noncomputable def positivePremium (μ : Measure ℝ) (w v : ℝ) : ℝ :=
  ∫ x, max (w * x - v) 0 ∂μ

lemma integrable_positivePart (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (w v : ℝ) : Integrable (fun x => max (w * x - v) 0) μ :=
  ((hμ.const_mul w).sub (integrable_const v)).sup (integrable_const 0)

lemma positivePremium_nonnegative (μ : Measure ℝ) (w v : ℝ) : 0 ≤ positivePremium μ w v :=
  integral_nonneg fun _ => le_max_right _ _

/-- Both laws have mass one, so a common continuation constant cancels from the
transition discrepancy. No unbiasedness or data-selection assertion is used. -/
lemma positivePremium_eq_max_sub (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (w v : ℝ) : positivePremium μ w v = expectedMaxWith μ w v - v := by
  have he : (fun x : ℝ => max (w * x - v) 0) = (fun x => max (w * x) v - v) := by
    funext x
    by_cases h : w * x ≤ v
    · simp [max_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    · have h' : v ≤ w * x := (lt_of_not_ge h).le
      simp [max_eq_left h', max_eq_left (sub_nonneg.mpr h')]
  unfold positivePremium expectedMaxWith
  rw [he, integral_sub (integrable_max_with μ hμ w v) (integrable_const v)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

lemma positivePremium_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (w : ℝ) : Continuous (positivePremium μ w) := by
  have he : positivePremium μ w = (fun v => expectedMaxWith μ w v - v) :=
    funext (positivePremium_eq_max_sub μ hμ w)
  rw [he]
  exact (expectedMaxWith_continuous μ hμ w).sub continuous_id

lemma positivePremium_le_firstMoment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (h0 : ∀ᵐ x ∂μ, 0 ≤ x) {w v : ℝ} (hw : 0 ≤ w) (hv : 0 ≤ v) :
    positivePremium μ w v ≤ w * ∫ x, x ∂μ := by
  have h := integral_mono_ae (integrable_positivePart μ hμ w v) (hμ.const_mul w)
    (h0.mono fun x hx => max_le (sub_le_self _ hv) (mul_nonneg hw hx))
  calc
    positivePremium μ w v ≤ ∫ x, w * x ∂μ := h
    _ = w * ∫ x, x ∂μ := integral_const_mul _ _

variable {n : ℕ}

/-- Forgetting observed values preserves the unseen identities, including identities
whose observed value was zero. -/
lemma unseen_history_values (D : Finset (Fin n)) (x y u : Fin n → ℝ) (t : ℝ) :
    unseen (history D x u t) = unseen (history D y u t) := by
  ext j
  simp only [unseen, Finset.mem_filter, Finset.mem_univ, true_and, history]
  split_ifs <;> simp

lemma Instance.continuationAtArrival_values_invariant (Q : Instance n) (w c : ℝ)
    (x y u : Fin n → ℝ) (i : Fin n) :
    Q.continuationAtArrival w c x u i = Q.continuationAtArrival w c y u i := by
  unfold Instance.continuationAtArrival
  rw [unseen_history_values Finset.univ x y u (u i)]

noncomputable def Instance.lawResidual (Q P : Instance n) (i : Fin n) (w v : ℝ) : ℝ :=
  positivePremium (Q.law i) w v - positivePremium (P.law i) w v

lemma Instance.lawResidual_eq_maxDifference (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin n) (w v : ℝ) :
    Q.lawResidual P i w v = expectedMaxWith (Q.law i) w v - expectedMaxWith (P.law i) w v := by
  rw [Instance.lawResidual, positivePremium_eq_max_sub (Q.law i) (Q.integrable_maximum_iff.mp hQ i),
    positivePremium_eq_max_sub (P.law i) (P.integrable_maximum_iff.mp hP i)]
  ring

lemma Instance.lawResidual_continuous (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin n) (w : ℝ) : Continuous (Q.lawResidual P i w) :=
  (positivePremium_continuous (Q.law i) (Q.integrable_maximum_iff.mp hQ i) w).sub
    (positivePremium_continuous (P.law i) (P.integrable_maximum_iff.mp hP i) w)

lemma Instance.abs_lawResidual_le (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin n) {w v : ℝ} (hw : 0 ≤ w) (hv : 0 ≤ v) :
    |Q.lawResidual P i w v| ≤ w * ((∫ x, x ∂Q.law i) + ∫ x, x ∂P.law i) := by
  calc
    |Q.lawResidual P i w v| ≤ |positivePremium (Q.law i) w v| + |positivePremium (P.law i) w v| :=
      by simpa only [Instance.lawResidual, sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (positivePremium (Q.law i) w v) 0 (positivePremium (P.law i) w v))
    _ = positivePremium (Q.law i) w v + positivePremium (P.law i) w v := by
      rw [abs_of_nonneg (positivePremium_nonnegative _ _ _), abs_of_nonneg (positivePremium_nonnegative _ _ _)]
    _ ≤ w * (∫ x, x ∂Q.law i) + w * (∫ x, x ∂P.law i) :=
      add_le_add (positivePremium_le_firstMoment (Q.law i) (Q.integrable_maximum_iff.mp hQ i) (Q.nonnegative i) hw hv)
        (positivePremium_le_firstMoment (P.law i) (P.integrable_maximum_iff.mp hP i) (P.nonnegative i) hw hv)
    _ = _ := by ring

/-- The complete clock vector is an analytical argument; the threshold uses exactly
the current time and the identities not observed before it. -/
noncomputable def Instance.transitionResidual (Q P : Instance n) (w c : ℝ)
    (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  Q.lawResidual P i w (Q.continuationAtArrival w c (fun _ => 0) u i)

noncomputable def Instance.firstTransitionResidual {m : ℕ} (Q P : Instance (m + 1))
    (i : Fin (m + 1)) (w c t : ℝ) : ℝ :=
  Q.lawResidual P i w (Q.bellmanContinuation i w c t)

variable {Ω Seed : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]

lemma Instance.measurable_transitionResidual (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) {u : Ω → Fin n → ℝ}
    (hu : ∀ j, Measurable fun ω => u ω j) (i : Fin n) :
    Measurable (fun ω => Q.transitionResidual P w c (u ω) i) :=
  (Q.lawResidual_continuous P hQ hP i w).measurable.comp
    (Q.measurable_continuationAtArrival hQ hw hc (fun _ => measurable_const) hu i)

lemma Instance.firstTransitionResidual_continuous {m : ℕ} (Q P : Instance (m + 1))
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (m + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Continuous (Q.firstTransitionResidual P i w c) :=
  (Q.lawResidual_continuous P hQ hP i w).comp (Q.bellmanContinuation_continuous hQ i hw hc)

omit [MeasurableSpace Seed] [MeasurableSpace Ω] in
lemma Instance.abs_transitionResidual_le (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (u : Fin n → ℝ) (i : Fin n) :
    |Q.transitionResidual P w c u i| ≤ w * ((∫ x, x ∂Q.law i) + ∫ x, x ∂P.law i) :=
  Q.abs_lawResidual_le P hQ hP i hw (Q.continuationAtArrival_nonnegative hQ hw hc _ u i)

noncomputable def Policy.reachedTransitionResidual (π : Policy Seed n) (Q P : Instance n)
    (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) : ℝ :=
  ∑ i, if π.Reaches r x u i then Q.transitionResidual P w c u i else 0

lemma Policy.measurable_reachedTransitionResidual (π : Policy Seed n) (hπ : π.IsMeasurable)
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    {r : Ω → Seed} {x u : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ j, Measurable fun ω => x ω j) (hu : ∀ j, Measurable fun ω => u ω j) :
    Measurable (fun ω => π.reachedTransitionResidual Q P w c (r ω) (x ω) (u ω)) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (π.measurableSet_reaches hπ hr hx hu i)
    (Q.measurable_transitionResidual P hQ hP hw hc hu i) measurable_const

omit [MeasurableSpace Ω] [MeasurableSpace Seed] in
lemma Policy.abs_reachedTransitionResidual_le (π : Policy Seed n) (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (r : Seed) (x u : Fin n → ℝ) :
    |π.reachedTransitionResidual Q P w c r x u| ≤ w * (Q.totalFirstMoment + P.totalFirstMoment) := by
  calc
    |π.reachedTransitionResidual Q P w c r x u| ≤
        ∑ i : Fin n, |if π.Reaches r x u i then Q.transitionResidual P w c u i else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, w * ((∫ x, x ∂Q.law i) + ∫ x, x ∂P.law i) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact Q.abs_transitionResidual_le P hQ hP hw hc u i
      · simpa only [abs_zero] using mul_nonneg hw (add_nonneg
          (integral_nonneg_of_ae (Q.nonnegative i)) (integral_nonneg_of_ae (P.nonnegative i)))
    _ = _ := by simp only [Instance.totalFirstMoment, Finset.mul_sum, Finset.sum_add_distrib, mul_add]

lemma Policy.integrable_reachedTransitionResidual (π : Policy Seed n) (hπ : π.IsMeasurable)
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (fun ω : World n Seed => π.reachedTransitionResidual Q P w c ω.2.2 ω.1 ω.2.1) (P.worldLaw ν) := by
  apply Integrable.of_bound (π.measurable_reachedTransitionResidual hπ Q P hQ hP hw hc
    (measurable_snd.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))).aestronglyMeasurable
    (w * (Q.totalFirstMoment + P.totalFirstMoment))
  exact Eventually.of_forall fun ω => by
    change ‖π.reachedTransitionResidual Q P w c ω.2.2 ω.1 ω.2.1‖ ≤ w * (Q.totalFirstMoment + P.totalFirstMoment)
    simpa only [Real.norm_eq_abs] using π.abs_reachedTransitionResidual_le Q P hQ hP hw.le hc ω.2.2 ω.1 ω.2.1

/-- The design-law action loss remains integrable when offers have another true law. -/
lemma Policy.integrable_reachedBellmanLoss_under (π : Policy Seed n) (hπ : π.IsMeasurable)
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (fun ω : World n Seed => π.reachedBellmanLoss Q w c ω.2.2 ω.1 ω.2.1) (P.worldLaw ν) := by
  have hp : MeasurePreserving (fun ω : World n Seed => ω.1) (P.worldLaw ν) P.valuesLaw := measurePreserving_fst
  have hB : Integrable (fun ω : World n Seed => ∑ i : Fin n, (w * ω.1 i + optimalScalarValue Q w c))
      (P.worldLaw ν) := by
    apply integrable_finsetSum
    intro i _
    exact ((hp.integrable_comp_of_integrable (P.integrable_coordinate_of_maximum hP i)).const_mul w).add
      (integrable_const _)
  apply hB.mono' (π.measurable_reachedBellmanLoss hπ Q hQ hw hc
    (measurable_snd.comp measurable_snd) (fun i => (measurable_pi_apply i).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))).aestronglyMeasurable
  filter_upwards [hp.quasiMeasurePreserving.ae P.ae_nonnegative, P.world_clocks_mem_unitInterval ν] with ω hx hu
  rw [Real.norm_eq_abs, abs_of_nonneg (π.reachedBellmanLoss_nonnegative Q w c _ _ _)]
  exact π.reachedBellmanLoss_le_sum Q hQ hw.le hc ω.2.2 ω.1 ω.2.1 hx (fun i => (hu i).1)

end ProphetSecretary.Model
