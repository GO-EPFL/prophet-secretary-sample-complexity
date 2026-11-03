import ProphetSecretary.Statistics.CalibratedLearnerRandomness
import ProphetSecretary.Statistics.NestedContinuation
import ProphetSecretary.Model.CappedThresholdFamily
import ProphetSecretary.Model.RankToClockMeasurability

/-!
# The actual ordered numerical policy family

At each arrival the callback receives only the empirical first block, active
unseen identities, remaining time, coefficient, and the current arrival's
query seed. Present zero-valued identities count toward the arrival position.
An empirically zero candidate is still tested against its child continuation.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {PSeed : Type*}

noncomputable def unitRemaining (t : ℝ) : ℝ := max 0 (min 1 (1-t))

lemma unitRemaining_range (t : ℝ) : unitRemaining t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma unitRemaining_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : unitRemaining t=1-t := by
  rw [unitRemaining, min_eq_right (by linarith [ht.1]), max_eq_right (by linarith [ht.2])]

lemma continuous_unitRemaining : Continuous unitRemaining := by unfold unitRemaining; fun_prop

noncomputable def continuationIdentities (y : Reservoir n m) (H : History n) (i : Fin n) : Finset (Fin n) :=
  ((unseen H).erase i).filter (fun j => ∃ l : Fin m, 0 < y j l)

lemma continuationIdentities_excludes_observed (y : Reservoir n m) (H : History n)
    (i j : Fin n) {t x : ℝ} (hj : H j = some (t,x)) : j ∉ continuationIdentities y H i := by
  simp [continuationIdentities, unseen, hj]

lemma measurable_continuationIdentities {Ω : Type*} [MeasurableSpace Ω]
    {y : Ω → Reservoir n m} {H : Ω → History n} {i : Ω → Fin n}
    (hy : ∀ q l, Measurable (fun ω => y ω q l)) (hH : Measurable H) (hi : Measurable i) :
    Measurable (fun ω => continuationIdentities (y ω) (H ω) (i ω)) := by
  rw [measurable_finset_iff]
  intro j
  apply measurableSet_setOf.mp
  have hn := measurableSet_observation_none.preimage ((measurable_pi_apply j).comp hH)
  have hne : MeasurableSet {ω | j ≠ i ω} :=
    (measurableSet_eq_fun (measurable_const (a := j)) hi).compl
  have hp : MeasurableSet {ω | ∃ l : Fin m, 0 < y ω j l} := by
    rw [Set.setOf_exists]
    exact MeasurableSet.iUnion (fun l => measurableSet_lt measurable_const (hy j l))
  convert (hne.inter hn).inter hp using 1
  ext ω
  simp [continuationIdentities, unseen]

def coefficientIndex (J k : ℕ) : Fin (J+1) := ⟨min k J, by omega⟩

noncomputable def familyCoefficient (zlo zhi : ℝ) (J k : ℕ) : ℝ :=
  zlo+((min k J : ℕ) : ℝ)/(J : ℝ)*(zhi-zlo)

lemma familyCoefficient_monotone {zlo zhi : ℝ} (hz : zlo ≤ zhi) (J : ℕ) :
    Monotone (familyCoefficient zlo zhi J) := by
  intro k l hkl
  have h : ((min k J : ℕ) : ℝ) ≤ ((min l J : ℕ) : ℝ) := by exact_mod_cast min_le_min hkl le_rfl
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right h (Nat.cast_nonneg J)) (sub_nonneg.mpr hz))

abbrev ContinuationEstimator (n m : ℕ) (PSeed : Type*) :=
  Reservoir n m → Finset (Fin n) → ℝ → ℝ → PSeed → ℝ

noncomputable def familyQuery (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (p : Reservoir n m × PolicyQueryArray n J PSeed) (t : ℝ) (i : Fin n) (H : History n) (k : ℕ) : ℝ :=
  estimate p.1 (continuationIdentities p.1 H i) (unitRemaining t) (familyCoefficient zlo zhi J k)
    (p.2 (currentRankFromClock i H, coefficientIndex J k))

noncomputable def familyThreshold (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (j : Fin (J+1)) (p : Reservoir n m × PolicyQueryArray n J PSeed)
    (t : ℝ) (i : Fin n) (H : History n) : ℝ :=
  ProphetSecretary.Statistics.nestedContinuation (familyCoefficient zlo zhi J)
    (familyQuery zlo zhi estimate p t i H) (unitRemaining t) j.val

lemma familyThreshold_mono {zlo zhi : ℝ} (hz : zlo ≤ zhi)
    (estimate : ContinuationEstimator n m PSeed) {j k : Fin (J+1)} (hjk : j ≤ k)
    (p : Reservoir n m × PolicyQueryArray n J PSeed) (t : ℝ) (i : Fin n) (H : History n) :
    familyThreshold zlo zhi estimate j p t i H ≤ familyThreshold zlo zhi estimate k p t i H := by
  exact ProphetSecretary.Statistics.nestedContinuation_monotone _ _
    (unitRemaining_range t).1 (familyCoefficient_monotone hz J) hjk

lemma measurable_familyQuery [MeasurableSpace PSeed] {Ω : Type*} [MeasurableSpace Ω]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (hEstimate : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
    {y : Ω → Reservoir n m} {r : Ω → PolicyQueryArray n J PSeed}
    {t : Ω → ℝ} {i : Ω → Fin n} {H : Ω → History n}
    (hy : Measurable y) (hr : Measurable r) (ht : Measurable t) (hi : Measurable i) (hH : Measurable H)
    (k : ℕ) : Measurable (fun ω => familyQuery zlo zhi estimate (y ω,r ω) (t ω) (i ω) (H ω) k) := by
  have hA := measurable_continuationIdentities (y := y)
    (fun q l => (measurable_pi_apply l).comp ((measurable_pi_apply q).comp hy)) hH hi
  have hPos := measurable_currentRankFromClock.comp (hi.prodMk hH)
  have hEval : Measurable (fun p : PolicyQueryArray n J PSeed × (Fin n × Fin (J+1)) => p.1 p.2) :=
    measurable_from_prod_countable_left (fun q => measurable_pi_apply q)
  have hSeed := hEval.comp (hr.prodMk (hPos.prodMk (measurable_const (a := coefficientIndex J k))))
  have hu := continuous_unitRemaining.measurable.comp ht
  exact hEstimate.comp (hy.prodMk (hA.prodMk (hu.prodMk (measurable_const.prodMk hSeed))))

lemma measurable_familyThreshold [MeasurableSpace PSeed] {Ω : Type*} [MeasurableSpace Ω]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (hEstimate : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
    (j : Fin (J+1)) {y : Ω → Reservoir n m} {r : Ω → PolicyQueryArray n J PSeed}
    {t : Ω → ℝ} {i : Ω → Fin n} {H : Ω → History n}
    (hy : Measurable y) (hr : Measurable r) (ht : Measurable t) (hi : Measurable i) (hH : Measurable H) :
    Measurable (fun ω => familyThreshold zlo zhi estimate j (y ω,r ω) (t ω) (i ω) (H ω)) := by
  have hu := continuous_unitRemaining.measurable.comp ht
  have hN : (Finset.range (j.val+1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  have hs : Measurable ((Finset.range (j.val+1)).sup' hN
      (fun k => fun ω => familyQuery zlo zhi estimate (y ω,r ω) (t ω) (i ω) (H ω) k)) := by
    apply Finset.measurable_sup'
    intro k _
    exact measurable_familyQuery zlo zhi estimate hEstimate hy hr ht hi hH k
  have hFloor : Measurable (fun ω => familyCoefficient zlo zhi J j.val*unitRemaining (t ω)) := measurable_const.mul hu
  have hmax := hFloor.max hs
  convert hmax using 1
  funext ω
  simp only [familyThreshold, ProphetSecretary.Statistics.nestedContinuation, Finset.sup'_apply]

def familyFallback [NeZero m] (y : Reservoir n m) : Prop :=
  targetCountCutoff m < empiricalPositiveCount (reservoirCoordinates y) ∨
    1/4 < (totalEmpiricalInstance y).expectedMaximum

noncomputable def numericalFamilyPolicy [NeZero m] (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (j : Fin (J+1)) : Policy (Reservoir n m × PolicyQueryArray n J PSeed) n where
  decide p t i x H := if familyFallback p.1 then decide (x=1) else
    (cappedHistoryThresholdPolicy (familyThreshold zlo zhi estimate j)).decide p t i x H

@[simp] lemma numericalFamilyPolicy_accepts_cap [NeZero m] (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (j : Fin (J+1)) (p) (t) (i) (H) : (numericalFamilyPolicy zlo zhi estimate j).decide p t i 1 H = true := by
  simp [numericalFamilyPolicy]

@[simp] lemma numericalFamilyPolicy_rejects_zero [NeZero m] (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (j : Fin (J+1)) (p) (t) (i) (H) : (numericalFamilyPolicy zlo zhi estimate j).decide p t i 0 H = false := by
  simp [numericalFamilyPolicy]

lemma numericalFamilyPolicy_isMeasurable [NeZero m] [MeasurableSpace PSeed] (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (hEstimate : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)) (j : Fin (J+1)) :
    (numericalFamilyPolicy zlo zhi estimate j).IsMeasurable := by
  let Ω := (Reservoir n m × PolicyQueryArray n J PSeed) × (ℝ × (Fin n × (ℝ × History n)))
  have hy : Measurable (fun q : Ω => q.1.1) := by fun_prop
  have hGuard : MeasurableSet {q : Ω | familyFallback q.1.1} :=
    (measurableSet_lt measurable_const (measurable_empiricalPositiveCount.comp (reservoirCoordinates.measurable.comp hy))).union
      (measurableSet_lt measurable_const (measurable_totalEmpirical_expectedMaximum (fun i l => by fun_prop)))
  have hCap : Measurable (fun q : Ω => decide (q.2.2.2.1=1)) := by
    apply measurable_to_bool
    change MeasurableSet {q : Ω | decide (q.2.2.2.1=1) = true}
    simp only [decide_eq_true_eq]
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  have hFamily := cappedHistoryThresholdPolicy_isMeasurable (familyThreshold zlo zhi estimate j)
    (measurable_familyThreshold zlo zhi estimate hEstimate j (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop) (by fun_prop))
  exact Measurable.ite hGuard hCap hFamily

/-- Coefficient ordering compares actual durations without deletion monotonicity. -/
lemma numericalFamilyPolicy_stoppingTime_mono [NeZero m] {zlo zhi : ℝ} (hz : zlo ≤ zhi)
    (estimate : ContinuationEstimator n m PSeed) {j k : Fin (J+1)} (hjk : j ≤ k)
    (p : Reservoir n m × PolicyQueryArray n J PSeed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    (numericalFamilyPolicy zlo zhi estimate j).stoppingTime p D x u ≤
      (numericalFamilyPolicy zlo zhi estimate k).stoppingTime p D x u := by
  apply Policy.stoppingTime_le_of_action_imp
  intro i hi ha
  simp only [Policy.action, numericalFamilyPolicy] at ha ⊢
  by_cases hg : familyFallback p.1
  · simpa only [if_pos hg] using ha
  · simp only [if_neg hg, cappedHistoryThresholdPolicy, decide_eq_true_eq] at ha ⊢
    exact ha.imp_right (fun h => ⟨h.1, (familyThreshold_mono hz estimate hjk p (u i) i
      (history D x u (u i))).trans h.2⟩)

end ProphetSecretary.Statistics.Calibration
