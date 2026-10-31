import ProphetSecretary.Model.BellmanResidual
import ProphetSecretary.Probability.CandidateValue
import ProphetSecretary.Reach.RareReach

/-!
# Canonical marginal acceptance premia

These premia are analytical conditional expectations over an independent
candidate value. Their energy bounds will identify the centered envelope
gradient once the one-marginal residual identity is applied.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.canonical_selects_of_reaches_of_gap (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (x u : Fin n → ℝ) (i : Fin n)
    (hr : (P.valuePolicy hP hw.le hc).rule.Reaches () x u i)
    (hg : P.continuationAtArrival w c x u i ≤ w * x i) :
    (P.valuePolicy hP hw.le hc).rule.Selects () Finset.univ x u i := by
  let π : Policy Unit n := (P.valuePolicy hP hw.le hc).rule
  have hact : π.action () Finset.univ x u i = true := by
    change Decidable.decide (P.valueThreshold w c (unseen (history Finset.univ x u (u i))) (u i) i ≤ x i) = true
    rw [decide_eq_true_eq]
    rw [P.continuationAtArrival_eq_threshold hw] at hg
    exact (mul_le_mul_iff_right₀ hw).mp hg
  have ha := (π.mem_accepted () Finset.univ x u i).mpr ⟨Finset.mem_univ _, hact⟩
  exact ⟨ha, le_antisymm hr (π.stoppingTime_le_of_accepted () Finset.univ x u i ha)⟩

noncomputable def Instance.reachedPremium (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (ω : World n Unit) : ℝ :=
  if (P.valuePolicy hP hw.le hc).rule.Reaches () ω.1 ω.2.1 i then
    max (w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i) 0 else 0

lemma Instance.reachedPremium_nonnegative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (ω : World n Unit) : 0 ≤ P.reachedPremium hP hw hc i ω := by
  unfold Instance.reachedPremium
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

lemma Instance.reachedPremium_le_selectedReward (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (ω : World n Unit) (hx : 0 ≤ ω.1 i) (hu : Function.Injective ω.2.1) :
    P.reachedPremium hP hw hc i ω ≤
      if (P.valuePolicy hP hw.le hc).rule.ActualSelects () Finset.univ ω.1 ω.2.1 i then w * ω.1 i else 0 := by
  let π : Policy Unit n := (P.valuePolicy hP hw.le hc).rule
  have hv := P.continuationAtArrival_nonnegative hP hw.le hc ω.1 ω.2.1 i
  change (if π.Reaches () ω.1 ω.2.1 i then max (w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i) 0 else 0) ≤
    if π.ActualSelects () Finset.univ ω.1 ω.2.1 i then w * ω.1 i else 0
  by_cases hs : π.ActualSelects () Finset.univ ω.1 ω.2.1 i
  · rw [if_pos hs]
    split_ifs
    · exact max_le (sub_le_self _ hv) (mul_nonneg hw.le hx)
    · exact mul_nonneg hw.le hx
  · rw [if_neg hs]
    split_ifs with hr
    · have hg : w * ω.1 i ≤ P.continuationAtArrival w c ω.1 ω.2.1 i := by
        by_contra hn
        have hsel := P.canonical_selects_of_reaches_of_gap hP hw hc ω.1 ω.2.1 i hr (le_of_not_ge hn)
        exact hs ((π.actualSelects_iff_selects () Finset.univ ω.1 ω.2.1 hu i).mpr hsel)
      rw [max_eq_right (sub_nonpos.mpr hg)]
    · exact le_rfl

lemma Instance.sum_reachedPremium_le_reward (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (ω : World n Unit) (hx : ∀ i, 0 ≤ ω.1 i) (hu : Function.Injective ω.2.1) :
    (∑ i : Fin n, P.reachedPremium hP hw hc i ω) ≤
      w * (P.valuePolicy hP hw.le hc).rule.reward () Finset.univ ω.1 ω.2.1 := by
  apply (Finset.sum_le_sum (fun i _ ↦ P.reachedPremium_le_selectedReward hP hw hc i ω (hx i) hu)).trans_eq
  rw [Policy.reward, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [mul_zero]

noncomputable def Instance.premiumAtValue (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (v : World n Unit × ℝ) : ℝ :=
  if (P.valuePolicy hP hw.le hc).rule.Reaches () (Function.update v.1.1 i v.2) v.1.2.1 i then
    max (w * v.2 - P.continuationAtArrival w c (fun _ ↦ 0) v.1.2.1 i) 0 else 0

noncomputable def Instance.marginalPremium (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (a : ℝ) : ℝ := ∫ ω : World n Unit, P.premiumAtValue hP hw hc i (ω, a) ∂P.worldLaw (Measure.dirac ())

lemma Instance.premiumAtValue_eq_replaced (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (v : World n Unit × ℝ) :
    P.premiumAtValue hP hw hc i v = P.reachedPremium hP hw hc i (Instance.replaceValue i v) := by
  let π : Policy Unit n := (P.valuePolicy hP hw.le hc).rule
  change (if π.Reaches () (Function.update v.1.1 i v.2) v.1.2.1 i then
      max (w * v.2 - P.continuationAtArrival w c (fun _ ↦ 0) v.1.2.1 i) 0 else 0) =
    (if π.Reaches () (Function.update v.1.1 i v.2) v.1.2.1 i then
      max (w * (Function.update v.1.1 i v.2) i - P.continuationAtArrival w c (Function.update v.1.1 i v.2) v.1.2.1 i) 0 else 0)
  rw [Function.update_self, P.continuationAtArrival_values_invariant w c (Function.update v.1.1 i v.2) (fun _ ↦ 0)]

lemma Instance.measurable_premiumAtValue (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (i : Fin n) :
    Measurable (P.premiumAtValue hP hw hc i) := by
  let π : Policy Unit n := (P.valuePolicy hP hw.le hc).rule
  have hπ : π.IsMeasurable := (P.valuePolicy hP hw.le hc).measurable_rule
  apply Measurable.ite (π.measurableSet_reaches hπ measurable_const
    (fun j ↦ by fun_prop) (fun j ↦ by fun_prop) i)
  · exact ((measurable_const.mul measurable_snd).sub
      (P.measurable_continuationAtArrival hP hw hc (fun _ ↦ measurable_const) (fun _ ↦ by fun_prop) i)).max measurable_const
  · exact measurable_const

lemma Instance.measurable_marginalPremium (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (i : Fin n) :
    Measurable (P.marginalPremium hP hw hc i) :=
  (P.measurable_premiumAtValue hP hw hc i).stronglyMeasurable.integral_prod_left'.measurable

lemma Instance.premiumAtValue_nonnegative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (v : World n Unit × ℝ) : 0 ≤ P.premiumAtValue hP hw hc i v := by
  unfold Instance.premiumAtValue
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

lemma Instance.premiumAtValue_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (v : World n Unit × ℝ) : P.premiumAtValue hP hw hc i v ≤ w * max v.2 0 := by
  have hv := P.continuationAtArrival_nonnegative hP hw.le hc (fun _ ↦ 0) v.1.2.1 i
  have hmax := mul_le_mul_of_nonneg_left (le_max_left v.2 0) hw.le
  have hzero := mul_nonneg hw.le (le_max_right v.2 0)
  unfold Instance.premiumAtValue
  split_ifs
  · exact max_le ((sub_le_self _ hv).trans hmax) hzero
  · exact hzero

lemma Instance.integrable_premiumAtValue_slice (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (a : ℝ) :
    Integrable (fun ω : World n Unit ↦ P.premiumAtValue hP hw hc i (ω, a)) (P.worldLaw (Measure.dirac ())) := by
  apply Integrable.of_bound ((P.measurable_premiumAtValue hP hw hc i).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (w * max a 0)
  exact Filter.Eventually.of_forall (fun ω ↦ by
    dsimp only [Function.comp_apply, id_eq]
    rw [Real.norm_eq_abs, abs_of_nonneg (P.premiumAtValue_nonnegative hP hw hc i (ω, a))]
    exact P.premiumAtValue_le hP hw hc i (ω, a))

lemma Instance.marginalPremium_nonnegative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (a : ℝ) : 0 ≤ P.marginalPremium hP hw hc i a :=
  integral_nonneg (fun ω ↦ P.premiumAtValue_nonnegative hP hw hc i (ω, a))

lemma Instance.marginalPremium_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (a : ℝ) : P.marginalPremium hP hw hc i a ≤ w * max a 0 := by
  have h := integral_mono (P.integrable_premiumAtValue_slice hP hw hc i a) (integrable_const (w * max a 0))
    (fun ω ↦ P.premiumAtValue_le hP hw hc i (ω, a))
  simpa only [Instance.marginalPremium, integral_const, probReal_univ, one_smul] using h

lemma Instance.integrable_premiumAtValue_joint (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H) (i : Fin n) :
    Integrable (P.premiumAtValue hP hw hc i) ((P.worldLaw (Measure.dirac ())).prod (P.law i)) := by
  apply Integrable.of_bound (P.measurable_premiumAtValue hP hw hc i).aestronglyMeasurable (w * H)
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := P.worldLaw (Measure.dirac ())) (ν := P.law i)).ae (hbound i)] with v hv
  rw [Real.norm_eq_abs, abs_of_nonneg (P.premiumAtValue_nonnegative hP hw hc i v)]
  exact (P.premiumAtValue_le hP hw hc i v).trans
    (mul_le_mul_of_nonneg_left (max_le hv hH) hw.le)

lemma Instance.integrable_marginalPremium (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H) (i : Fin n) :
    Integrable (P.marginalPremium hP hw hc i) (P.law i) :=
  (P.integrable_premiumAtValue_joint hP hw hc hH hbound i).integral_prod_right

lemma Instance.measurable_reachedPremium (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (i : Fin n) :
    Measurable (P.reachedPremium hP hw hc i) := by
  let π : Policy Unit n := (P.valuePolicy hP hw.le hc).rule
  have hπ : π.IsMeasurable := (P.valuePolicy hP hw.le hc).measurable_rule
  exact Measurable.ite (π.measurableSet_reaches hπ measurable_const
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i)
    (((measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).sub
      (P.measurable_continuationAtArrival hP hw hc
        (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
        (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i)).max measurable_const)
    measurable_const

lemma Instance.integrable_reachedPremium (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H) (i : Fin n) :
    Integrable (P.reachedPremium hP hw hc i) (P.worldLaw (Measure.dirac ())) := by
  have hrep := P.replaceValue_measurePreserving (Measure.dirac ()) i
  apply (hrep.integrable_comp (P.measurable_reachedPremium hP hw hc i).aestronglyMeasurable).mp
  exact (P.integrable_premiumAtValue_joint hP hw hc hH hbound i).congr
    (Filter.Eventually.of_forall (P.premiumAtValue_eq_replaced hP hw hc i))

lemma Instance.integral_marginalPremium (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H) (i : Fin n) :
    (∫ a, P.marginalPremium hP hw hc i a ∂P.law i) =
      ∫ ω : World n Unit, P.reachedPremium hP hw hc i ω ∂P.worldLaw (Measure.dirac ()) := by
  unfold Instance.marginalPremium
  rw [← integral_prod_symm _ (P.integrable_premiumAtValue_joint hP hw hc hH hbound i)]
  have hrep := P.replaceValue_measurePreserving (Measure.dirac ()) i
  have he := integral_map (μ := (P.worldLaw (Measure.dirac ())).prod (P.law i)) hrep.measurable.aemeasurable
    (P.measurable_reachedPremium hP hw hc i).aestronglyMeasurable
  rw [hrep.map_eq] at he
  rw [he]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (P.premiumAtValue_eq_replaced hP hw hc i)

lemma Instance.marginalPremium_le_reach (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H a : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (ha : a ≤ H) (i : Fin n) :
    P.marginalPremium hP hw hc i a ≤ w * H *
      (P.valuePolicy hP hw.le hc).rule.reachProbability P (Measure.dirac ()) i := by
  let π : Policy Unit n := (P.valuePolicy hP hw.le hc).rule
  have hπ : π.IsMeasurable := (P.valuePolicy hP hw.le hc).measurable_rule
  let E : Set (World n Unit) := {ω | π.Reaches () ω.1 ω.2.1 i}
  have hE : MeasurableSet E := π.measurableSet_reaches hπ measurable_const
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have heq : (P.worldLaw (Measure.dirac ())).real E = π.reachProbability P (Measure.dirac ()) i := by
    rfl
  have hp : ∀ᵐ ω : World n Unit ∂P.worldLaw (Measure.dirac ()),
      P.premiumAtValue hP hw hc i (ω, a) ≤ E.indicator (fun _ ↦ w * H) ω := by
    filter_upwards [P.world_clocks_mem_unitInterval (Measure.dirac ())] with ω hω
    have hr := π.reaches_update_value () ω.1 ω.2.1 i a (hω i).2
    change (if π.Reaches () (Function.update ω.1 i a) ω.2.1 i then
      max (w * a - P.continuationAtArrival w c (fun _ ↦ 0) ω.2.1 i) 0 else 0) ≤ _
    simp only [hr]
    by_cases he : π.Reaches () ω.1 ω.2.1 i
    · rw [Set.indicator_of_mem (s := E) he, if_pos he]
      exact max_le ((sub_le_self _ (P.continuationAtArrival_nonnegative hP hw.le hc (fun _ ↦ 0) ω.2.1 i)).trans
        (mul_le_mul_of_nonneg_left ha hw.le)) (mul_nonneg hw.le hH)
    · rw [Set.indicator_of_notMem (s := E) he, if_neg he]
  have hi := integral_mono_ae (P.integrable_premiumAtValue_slice hP hw hc i a)
    ((integrable_const (w * H)).indicator hE) hp
  rw [integral_indicator_const _ hE, smul_eq_mul, heq] at hi
  have hi' := hi
  rw [mul_comm] at hi'
  convert hi' using 1 <;> rfl

lemma Instance.marginalPremium_le_duration (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H a : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (ha : a ≤ H) (i : Fin n) :
    P.marginalPremium hP hw hc i a ≤ 2 * w * H * (P.valuePolicy hP hw.le hc).expectedDuration P := by
  let C := P.valuePolicy hP hw.le hc
  have hreach := C.rule.reachProbability_le_twice_meanDuration C.measurable_rule P C.seedLaw i
  calc
    _ ≤ w * H * C.rule.reachProbability P C.seedLaw i := P.marginalPremium_le_reach hP hw hc hH ha i
    _ ≤ w * H * (2 * C.rule.meanDuration P C.seedLaw) :=
      mul_le_mul_of_nonneg_left hreach (mul_nonneg hw.le hH)
    _ = _ := by
      change w * H * (2 * C.expectedDuration P) = _
      ring

lemma Instance.sum_integral_marginalPremium_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H) :
    (∑ i : Fin n, ∫ a, P.marginalPremium hP hw hc i a ∂P.law i) ≤
      w * (P.valuePolicy hP hw.le hc).expectedReward P := by
  simp_rw [P.integral_marginalPremium hP hw hc hH hbound]
  rw [← integral_finsetSum Finset.univ (fun i _ ↦ P.integrable_reachedPremium hP hw hc hH hbound i)]
  let C := P.valuePolicy hP hw.le hc
  have hp : MeasurePreserving (fun ω : World n Unit ↦ ω.1) (P.worldLaw (Measure.dirac ())) P.valuesLaw := measurePreserving_fst
  have h := integral_mono_ae
    (integrable_finsetSum _ (fun i _ ↦ P.integrable_reachedPremium hP hw hc hH hbound i))
    ((C.integrable_realizedReward P hP).const_mul w) (by
      filter_upwards [hp.quasiMeasurePreserving.ae P.ae_nonnegative,
        P.world_clocks_distinct (Measure.dirac ())] with ω hx hu
      have hr : ω.2.2 = () := Subsingleton.elim _ _
      change (∑ i : Fin n, P.reachedPremium hP hw hc i ω) ≤ w * C.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1
      rw [hr]
      exact P.sum_reachedPremium_le_reward hP hw hc ω hx hu)
  rw [integral_const_mul] at h
  convert h using 1 <;> rfl

end ProphetSecretary.Model
