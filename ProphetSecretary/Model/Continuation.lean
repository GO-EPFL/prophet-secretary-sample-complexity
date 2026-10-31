import ProphetSecretary.Model.Restriction
import ProphetSecretary.Model.ScalarValueProperties
import ProphetSecretary.Reach.FiniteStrictReach
import Mathlib.Data.Finset.Sort

/-!
# Finite continuation values and value thresholds

The finite law `P_A` uses the identities in `A`, enumerated in increasing order.
Continuation values optimize over every admissible randomized policy. Their
monotonicity and continuity give measurable monotone value thresholds. Optimality
of these threshold rules requires the separate Bellman argument.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- Increasing-order enumeration of the original identities in a state. -/
def stateEmbedding (A : Finset (Fin n)) : Fin A.card ↪ Fin n :=
  (A.orderEmbOfFin rfl).toEmbedding

/-- Inclusion of two unseen sets, expressed in their finite enumerations. -/
noncomputable def stateInclusion {A B : Finset (Fin n)} (hAB : A ⊆ B) : Fin A.card ↪ Fin B.card where
  toFun k := (B.orderIsoOfFin rfl).symm
    ⟨stateEmbedding A k, hAB (A.orderEmbOfFin_mem rfl k)⟩
  inj' := by
    intro k l h
    apply (stateEmbedding A).injective
    exact congrArg (fun z : B ↦ (z : Fin n)) ((B.orderIsoOfFin rfl).symm.injective h)


theorem stateInclusion_commutes {A B : Finset (Fin n)} (hAB : A ⊆ B) (k : Fin A.card) :
    stateEmbedding B (stateInclusion hAB k) = stateEmbedding A k := by
  change ((B.orderIsoOfFin rfl) ((B.orderIsoOfFin rfl).symm
    ⟨stateEmbedding A k, hAB (A.orderEmbOfFin_mem rfl k)⟩) : Fin n) = _
  simp only [OrderIso.apply_symm_apply]

namespace Instance

/-- The product law on a finite set of unseen identities, with its labels retained
by the increasing-order embedding into the original instance. -/
def restrictTo (P : Instance n) (A : Finset (Fin n)) : Instance A.card :=
  P.restrictBy (stateEmbedding A)

lemma eq_of_law_eq {m : ℕ} {P Q : Instance m} (h : P.law = Q.law) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

lemma restrictTo_restrictBy (P : Instance n) {A B : Finset (Fin n)} (hAB : A ⊆ B) :
    (P.restrictTo B).restrictBy (stateInclusion hAB) = P.restrictTo A := by
  apply eq_of_law_eq
  funext k
  change P.law (stateEmbedding B (stateInclusion hAB k)) = P.law (stateEmbedding A k)
  rw [stateInclusion_commutes]

lemma restrictTo_integrable_maximum (P : Instance n) (A : Finset (Fin n))
    (hP : Integrable maximum P.valuesLaw) : Integrable maximum (P.restrictTo A).valuesLaw :=
  P.restrictBy_integrable_maximum (stateEmbedding A) hP

/-- Adding unseen options can never reduce continuation value: the larger
observer can causally simulate a policy that ignores all the extra identities. -/
lemma optimalScalarValue_restrictTo_mono (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) {A B : Finset (Fin n)} (hAB : A ⊆ B)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue (P.restrictTo A) w c ≤ optimalScalarValue (P.restrictTo B) w c := by
  have h := optimalScalarValue_restrictBy_le (P.restrictTo B) (stateInclusion hAB)
    (P.restrictTo_integrable_maximum B hP) hw hc
  rw [P.restrictTo_restrictBy hAB] at h
  exact h

/-- Optimal additional continuation value, excluding accrued duration payoff. -/
noncomputable def continuationValue (P : Instance n) (A : Finset (Fin n)) (u w c : ℝ) : ℝ :=
  optimalScalarValue (P.restrictTo A) w (c * u)

/-- The manuscript's scalar value threshold at elapsed time `t`. The truncation
of remaining time outside `[0,1]` only supplies a total measurable decision rule. -/
noncomputable def valueThreshold (P : Instance n) (w c : ℝ)
    (A : Finset (Fin n)) (t : ℝ) (i : Fin n) : ℝ :=
  P.continuationValue (A.erase i) (max 0 (1 - t)) w c / w

lemma valueThreshold_continuous (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (A : Finset (Fin n)) (i : Fin n) :
    Continuous (fun t ↦ P.valueThreshold w c A t i) := by
  have hV := optimalScalarValue_durationWeight_continuousOn (P.restrictTo (A.erase i))
    (P.restrictTo_integrable_maximum (A.erase i) hP) hw
  have ht : Continuous (fun t : ℝ ↦ c * max 0 (1 - t)) :=
    continuous_const.mul (continuous_const.max (continuous_const.sub continuous_id))
  have hcomp := hV.comp_continuous ht (fun t ↦ mul_nonneg hc (le_max_left _ _))
  exact hcomp.div_const w

lemma valueThreshold_jointMeasurable (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Measurable (fun z : Finset (Fin n) × (Fin n × ℝ) ↦ P.valueThreshold w c z.1 z.2.2 z.2.1) := by
  apply measurable_from_prod_countable_right
  intro A
  apply measurable_from_prod_countable_right
  intro i
  exact (P.valueThreshold_continuous hP hw hc A i).measurable

lemma valueThreshold_monotone (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    MonotoneThresholds (fun (_ : Unit) A t i ↦ P.valueThreshold w c A t i) := by
  intro _r t i A B _hi hAB
  apply div_le_div_of_nonneg_right _ hw.le
  exact P.optimalScalarValue_restrictTo_mono hP (Finset.erase_subset_erase i hAB) hw.le
    (mul_nonneg hc (le_max_left _ _))

lemma continuationValue_nonnegative (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) (A : Finset (Fin n)) {u w c : ℝ}
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    0 ≤ P.continuationValue A u w c :=
  optimalScalarValue_nonnegative (P.restrictTo A) (P.restrictTo_integrable_maximum A hP)
    hw (mul_nonneg hc hu)

/-- More remaining time cannot reduce the additional continuation value. -/
lemma continuationValue_horizon_mono (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) (A : Finset (Fin n)) {u v w c : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    P.continuationValue A u w c ≤ P.continuationValue A v w c :=
  optimalScalarValue_mono (P.restrictTo A) (P.restrictTo_integrable_maximum A hP)
    hw (mul_nonneg hc hu) le_rfl (mul_le_mul_of_nonneg_left huv hc)

/-- Waiting to the terminal time is always available. -/
lemma durationWeight_le_continuationValue (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) (A : Finset (Fin n)) {u w c : ℝ}
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    c * u ≤ P.continuationValue A u w c :=
  durationWeight_le_optimalScalarValue (P.restrictTo A) (P.restrictTo_integrable_maximum A hP)
    hw (mul_nonneg hc hu)

/-- With positive reward and duration coefficients, all preterminal value
thresholds are positive, including for a zero-mean continuation instance. -/
lemma valueThreshold_positive (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) {w c t : ℝ}
    (hw : 0 < w) (hc : 0 < c) (ht : t < 1)
    (A : Finset (Fin n)) (i : Fin n) : 0 < P.valueThreshold w c A t i := by
  apply div_pos _ hw
  have hu : 0 < max 0 (1 - t) := lt_max_of_lt_right (sub_pos.mpr ht)
  exact lt_of_lt_of_le (mul_pos hc hu)
    (P.durationWeight_le_continuationValue hP (A.erase i) hu.le hw.le hc.le)

/-- Additional continuation after any nonnegative elapsed time cannot exceed
the initial optimized scalar value. This is the cap-acceptance comparison. -/
lemma valueThreshold_le_initialValue (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) {w c t : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (A : Finset (Fin n)) (i : Fin n) :
    P.valueThreshold w c A t i ≤ optimalScalarValue P w c / w := by
  apply div_le_div_of_nonneg_right _ hw.le
  have hu : max 0 (1 - t) ≤ 1 := max_le zero_le_one (by linarith)
  have hcu : c * max 0 (1 - t) ≤ c := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu hc
  exact (optimalScalarValue_mono (P.restrictTo (A.erase i))
    (P.restrictTo_integrable_maximum (A.erase i) hP) hw.le
    (mul_nonneg hc (le_max_left _ _)) le_rfl hcu).trans
      (optimalScalarValue_restrictBy_le P (stateEmbedding (A.erase i)) hP hw.le hc)

/-- The derivative sign convention in the paper: thresholds are nonincreasing
in elapsed time, whereas continuation is nondecreasing in remaining horizon. -/
lemma valueThreshold_antitone_elapsedTime (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (A : Finset (Fin n)) (i : Fin n) : Antitone (fun t ↦ P.valueThreshold w c A t i) := by
  intro t s hts
  apply div_le_div_of_nonneg_right _ hw.le
  apply P.continuationValue_horizon_mono hP (A.erase i) (le_max_left _ _)
  · exact max_le_max le_rfl (sub_le_sub_left hts 1)
  · exact hw.le
  · exact hc

end Instance

/-- The unseen-identity set is a measurable function of the complete history.
In particular, an observed zero value counts as an observation. -/
lemma measurable_unseen : Measurable (unseen (n := n)) := by
  let code : Option (ℝ × ℝ) → Unit ⊕ (ℝ × ℝ) :=
    fun o ↦ match o with | none => Sum.inl () | some p => Sum.inr p
  have hc : Measurable code := Measurable.of_comap_le le_rfl
  have hn : MeasurableSet {o : Option (ℝ × ℝ) | o = none} := by
    convert hc (measurableSet_range_inl (α := Unit) (β := ℝ × ℝ)) using 1
    ext o
    cases o <;> simp [code]
  rw [measurable_finset_iff]
  intro i
  apply measurableSet_setOf.mp
  simpa only [unseen, Finset.mem_filter, Finset.mem_univ, true_and, Set.preimage_setOf_eq] using
    hn.preimage (measurable_pi_apply i)

/-- Jointly measurable value thresholds define an admissible online policy.
No optimality conclusion is included here. -/
lemma Instance.valueThreshold_policy_isMeasurable (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (thresholdPolicy (fun (_ : Unit) A t i ↦ P.valueThreshold w c A t i)).IsMeasurable := by
  classical
  let T := Unit × (ℝ × (Fin n × (ℝ × History n)))
  have hmH : Measurable (fun z : T ↦ unseen z.2.2.2.2) :=
    measurable_unseen.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hmt : Measurable (fun z : T ↦ z.2.1) := measurable_fst.comp measurable_snd
  have hmi : Measurable (fun z : T ↦ z.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hmx : Measurable (fun z : T ↦ z.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hth := (P.valueThreshold_jointMeasurable hP hw hc).comp (hmH.prodMk (hmi.prodMk hmt))
  have hcond := measurableSet_le hth hmx
  change Measurable (fun z : T ↦ decide (P.valueThreshold w c (unseen z.2.2.2.2) z.2.1 z.2.2.1 ≤ z.2.2.2.1))
  have hIf : Measurable (fun z : T ↦ if P.valueThreshold w c (unseen z.2.2.2.2) z.2.1 z.2.2.1 ≤ z.2.2.2.1 then true else false) :=
    Measurable.ite hcond measurable_const measurable_const
  convert hIf using 1
  funext z
  split_ifs <;> simp_all

/-- Every reached offer at least the initial scalar value divided by `w` is
accepted, including ties. This proof establishes threshold behavior only. -/
theorem Instance.valueThreshold_accepts_cap (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (x u : Fin n → ℝ) (i : Fin n) (ht : 0 ≤ u i)
    (hx : optimalScalarValue P w c / w ≤ x i) :
    (thresholdPolicy (fun (_ : Unit) A t j ↦ P.valueThreshold w c A t j)).action
      () Finset.univ x u i = true := by
  change decide (P.valueThreshold w c (unseen (history Finset.univ x u (u i))) (u i) i ≤ x i) = true
  exact decide_eq_true ((P.valueThreshold_le_initialValue hP hw hc ht _ i).trans hx)

/-- Positive-duration value thresholds reject a zero observation before the
terminal time, but still retain its identity in subsequent histories. -/
theorem Instance.valueThreshold_rejects_zero (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (x u : Fin n → ℝ) (i : Fin n) (ht : u i < 1) (hx : x i = 0) :
    (thresholdPolicy (fun (_ : Unit) A t j ↦ P.valueThreshold w c A t j)).action
      () Finset.univ x u i = false := by
  have hp := P.valueThreshold_positive hP hw hc ht
    (unseen (history Finset.univ x u (u i))) i
  change decide (P.valueThreshold w c (unseen (history Finset.univ x u (u i))) (u i) i ≤ x i) = false
  rw [hx]
  simp only [not_le.mpr hp, decide_false]

/-- The strict finite reach bound for value thresholds, even when their design
law `P` differs from the evaluation law `Q`. Existence of a canonical optimizer
is a separate dependency of the manuscript. -/
theorem Instance.valueThreshold_strict_reach (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (Q : Instance n) (i : Fin n) :
    let π := thresholdPolicy (fun (_ : Unit) A t j ↦ P.valueThreshold w c A t j)
    π.reachProbability Q (Measure.dirac ()) i - π.meanDuration Q (Measure.dirac ()) ≥
      (π.selectionProbability Q (Measure.dirac ()) i) ^ 2 / 2 := by
  exact thresholdPolicy.strict_reach _ (P.valueThreshold_monotone hP hw hc)
    (P.valueThreshold_policy_isMeasurable hP hw.le hc) Q (Measure.dirac ()) i

end ProphetSecretary.Model
