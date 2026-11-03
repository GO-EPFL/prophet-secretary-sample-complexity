import ProphetSecretary.Statistics.PlannerRoundedSampler

/-!
# The four rounded-sampler error envelopes

The identity and time-threshold envelopes use the ideal first subset. Its
randomness belongs to the first product factor. The fresh identity, maximum
and tail reservoirs occupy the remaining independent factors.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def plannerChoiceRoundingEvent {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (N : ℕ) (hN : 0 < N) : Set (PlannerUniformSeed n) :=
  {s | plannerFirstSuccessChoice A p hA s.1.1 ≠
    plannerFirstSuccessChoice A p hA (uniformGridRound N hN s.1.1)}

noncomputable def plannerCoinRoundingEvent {n : ℕ} (p : Fin n → ℝ) (N : ℕ) (hN : 0 < N) :
    Set (PlannerUniformSeed n) :=
  {s | ∃ i : Fin n, decide (s.1.2 i ≤ plannerBernoulliProbability (p i)) ≠
    decide (uniformGridRound N hN (s.1.2 i) ≤ plannerBernoulliProbability (p i))}

noncomputable def plannerIdentityRoundingEvent {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (N : ℕ) (hN : 0 < N) : Set (PlannerUniformSeed n) :=
  {s | plannerTotalIdentity (plannerRecordedSubset A p s.1) s.2.1 ≠
    plannerTotalIdentity (plannerRecordedSubset A p s.1) (uniformGridRound N hN s.2.1)}

noncomputable def plannerTailRoundingEvent {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (N : ℕ) (hN : 0 < N) : Set (PlannerUniformSeed n) :=
  {s | ∃ i : Fin n,
    decide (s.2.2.2 i ≤ plannerTotalFraction (plannerRecordedSubset A p s.1) s.2.2.1) ≠
    decide (uniformGridRound N hN (s.2.2.2 i) ≤
      plannerTotalFraction (plannerRecordedSubset A p s.1) (plannerRoundVector N hN s.2.2.1))}

lemma plannerChoiceRoundingEvent_probability {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (N : ℕ) (hN : 0 < N) :
    (plannerUniformSeedLaw n).real (plannerChoiceRoundingEvent A p hA N hN) ≤ (n : ℝ) / N := by
  have hp : MeasurePreserving (fun s : PlannerUniformSeed n => s.1.1)
      (plannerUniformSeedLaw n) Instance.uniformClock := measurePreserving_fst.comp measurePreserving_fst
  have hm : MeasurableSet {u | plannerFirstSuccessChoice A p hA u ≠
      plannerFirstSuccessChoice A p hA (uniformGridRound N hN u)} :=
    (measurableSet_eq_fun (measurable_plannerFirstSuccessChoice A p hA)
      ((measurable_plannerFirstSuccessChoice A p hA).comp (measurable_uniformGridRound N hN))).compl
  have he := hp.hasLaw.measureReal_eq hm
  have hb := categoricalUniformSample_rounded_probability A hA (plannerFirstSuccessWeight A p) N hN
  have hcN : A.card ≤ n := by simpa only [Fintype.card_fin] using A.card_le_univ
  have hc : (A.card : ℝ) ≤ n := by exact_mod_cast hcN
  exact he.le.trans (hb.trans (div_le_div_of_nonneg_right hc (Nat.cast_nonneg N)))

lemma plannerCoinRoundingEvent_probability {n : ℕ} (p : Fin n → ℝ) (N : ℕ) (hN : 0 < N) :
    (plannerUniformSeedLaw n).real (plannerCoinRoundingEvent p N hN) ≤ (n : ℝ) / N := by
  have hp : MeasurePreserving (fun s : PlannerUniformSeed n => s.1.2)
      (plannerUniformSeedLaw n) (Instance.clocksLaw n) := measurePreserving_snd.comp measurePreserving_fst
  have hm : MeasurableSet {u : Fin n → ℝ | ∃ i : Fin n,
      decide (u i ≤ plannerBernoulliProbability (p i)) ≠
        decide (uniformGridRound N hN (u i) ≤ plannerBernoulliProbability (p i))} := by
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion (fun i => measurableSet_decide_disagreement _ _
      (measurableSet_le (measurable_pi_apply i) measurable_const)
      (measurableSet_le ((measurable_uniformGridRound N hN).comp (measurable_pi_apply i)) measurable_const))
  have he := hp.hasLaw.measureReal_eq hm
  have hb := rounded_vector_comparison_probability Finset.univ
    (fun i : Fin n => plannerBernoulliProbability (p i)) N hN
  apply he.le.trans
  simpa only [Finset.mem_univ, true_and, Finset.card_univ, Fintype.card_fin] using hb

lemma plannerIdentityRoundingEvent_measurable {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (N : ℕ) (hN : 0 < N) : MeasurableSet (plannerIdentityRoundingEvent A p N hN) := by
  have hd : Measurable (fun s : PlannerUniformSeed n => plannerRecordedSubset A p s.1) :=
    (measurable_plannerRecordedSubset A p).comp measurable_fst
  have hu : Measurable (fun s : PlannerUniformSeed n => s.2.1) := measurable_fst.comp measurable_snd
  exact (measurableSet_eq_fun ((measurable_plannerTotalIdentity_joint n).comp (hd.prodMk hu))
    ((measurable_plannerTotalIdentity_joint n).comp
      (hd.prodMk ((measurable_uniformGridRound N hN).comp hu)))).compl

lemma plannerIdentityRoundingEvent_probability {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (N : ℕ) (hN : 0 < N) :
    (plannerUniformSeedLaw n).real (plannerIdentityRoundingEvent A p N hN) ≤ (n : ℝ) / N := by
  apply product_event_probability_le
    (Instance.uniformClock.prod (Instance.clocksLaw n)) (plannerUniformTailSeedLaw n)
    (plannerIdentityRoundingEvent A p N hN) (plannerIdentityRoundingEvent_measurable A p N hN)
  exact ae_of_all _ (fun first => by
    let D := plannerRecordedSubset A p first
    have hm : MeasurableSet {u | plannerTotalIdentity D u ≠
        plannerTotalIdentity D (uniformGridRound N hN u)} :=
      (measurableSet_eq_fun (measurable_plannerTotalIdentity D)
        ((measurable_plannerTotalIdentity D).comp (measurable_uniformGridRound N hN))).compl
    have hp : MeasurePreserving (fun s : PlannerUniformTailSeed n => s.1)
        (plannerUniformTailSeedLaw n) Instance.uniformClock := measurePreserving_fst
    exact (hp.hasLaw.measureReal_eq hm).le.trans (plannerTotalIdentity_rounded_probability D N hN))

noncomputable def plannerFixedTailRoundingEvent {n : ℕ} (D : Finset (Fin n)) (N : ℕ) (hN : 0 < N) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {s | ∃ i : Fin n, decide (s.2 i ≤ plannerTotalFraction D s.1) ≠
    decide (uniformGridRound N hN (s.2 i) ≤ plannerTotalFraction D (plannerRoundVector N hN s.1))}

lemma plannerFixedTailRoundingEvent_measurable {n : ℕ} (D : Finset (Fin n)) (N : ℕ) (hN : 0 < N) :
    MeasurableSet (plannerFixedTailRoundingEvent D N hN) := by
  have ht : Measurable (fun s : (Fin n → ℝ) × (Fin n → ℝ) => plannerTotalFraction D s.1) :=
    (measurable_plannerTotalFraction D).comp measurable_fst
  have htr : Measurable (fun s : (Fin n → ℝ) × (Fin n → ℝ) =>
      plannerTotalFraction D (plannerRoundVector N hN s.1)) :=
    (measurable_plannerTotalFraction D).comp ((measurable_plannerRoundVector n N hN).comp measurable_fst)
  change MeasurableSet {s | ∃ i : Fin n, _}
  simp only [Set.setOf_exists]
  exact MeasurableSet.iUnion (fun i => measurableSet_decide_disagreement _ _
    (measurableSet_le ((measurable_pi_apply i).comp measurable_snd) ht)
    (measurableSet_le ((measurable_uniformGridRound N hN).comp
      ((measurable_pi_apply i).comp measurable_snd)) htr))

lemma plannerFixedTailRoundingEvent_probability {n : ℕ} (D : Finset (Fin n)) (N : ℕ) (hN : 0 < N) :
    ((Instance.clocksLaw n).prod (Instance.clocksLaw n)).real
      (plannerFixedTailRoundingEvent D N hN) ≤ 4 * (n : ℝ) / N := by
  apply product_event_probability_le (Instance.clocksLaw n) (Instance.clocksLaw n)
    (plannerFixedTailRoundingEvent D N hN) (plannerFixedTailRoundingEvent_measurable D N hN)
  filter_upwards [Instance.clocks_mem_unitInterval (n := n)] with u hu
  change (Instance.clocksLaw n).real {v | ∃ i : Fin n,
    decide (v i ≤ plannerTotalFraction D u) ≠
      decide (uniformGridRound N hN (v i) ≤ plannerTotalFraction D (plannerRoundVector N hN u))} ≤ _
  have ht := plannerTotalFraction_round_error D N hN u hu
  have hb := rounded_vector_moving_comparison_probability (Finset.univ : Finset (Fin n))
    (plannerTotalFraction D u) (plannerTotalFraction D (plannerRoundVector N hN u)) N hN ht
  simpa only [Finset.mem_univ, true_and, Finset.card_univ, Fintype.card_fin] using hb

lemma plannerTailRoundingEvent_measurable {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (N : ℕ) (hN : 0 < N) : MeasurableSet (plannerTailRoundingEvent A p N hN) := by
  have hd : Measurable (fun s : PlannerUniformSeed n => plannerRecordedSubset A p s.1) :=
    (measurable_plannerRecordedSubset A p).comp measurable_fst
  have hu : Measurable (fun s : PlannerUniformSeed n => s.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have ht := (measurable_plannerTotalFraction_joint n).comp (hd.prodMk hu)
  have htr := (measurable_plannerTotalFraction_joint n).comp
    (hd.prodMk ((measurable_plannerRoundVector n N hN).comp hu))
  change MeasurableSet {s | ∃ i : Fin n, _}
  simp only [Set.setOf_exists]
  exact MeasurableSet.iUnion (fun i => measurableSet_decide_disagreement _ _
    (measurableSet_le ((measurable_pi_apply i).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))) ht)
    (measurableSet_le ((measurable_uniformGridRound N hN).comp
      ((measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))) htr))

lemma plannerTailRoundingEvent_probability {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (N : ℕ) (hN : 0 < N) :
    (plannerUniformSeedLaw n).real (plannerTailRoundingEvent A p N hN) ≤ 4 * (n : ℝ) / N := by
  apply product_event_probability_le
    (Instance.uniformClock.prod (Instance.clocksLaw n)) (plannerUniformTailSeedLaw n)
    (plannerTailRoundingEvent A p N hN) (plannerTailRoundingEvent_measurable A p N hN)
  exact ae_of_all _ (fun first => by
    let D := plannerRecordedSubset A p first
    have hp : MeasurePreserving (fun s : PlannerUniformTailSeed n => s.2)
        (plannerUniformTailSeedLaw n) ((Instance.clocksLaw n).prod (Instance.clocksLaw n)) :=
      measurePreserving_snd
    exact (hp.hasLaw.measureReal_eq (plannerFixedTailRoundingEvent_measurable D N hN)).le.trans
      (plannerFixedTailRoundingEvent_probability D N hN))

end ProphetSecretary.Statistics
