import ProphetSecretary.Model.MarginalPremium
import ProphetSecretary.Probability.MarginalReplacement

/-!
# Scored marginal acceptance premia

Conditioning the candidate value separates its centered likelihood score from
the pending execution. The equality is derived by product integration and the
pathwise erasure property, including all observed zero identities.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.marginalScorePremium (P : Instance n) (w c : ℝ) (i : Fin n)
    (h : ℝ → ℝ) (u : Fin n → ℝ) : ℝ :=
  ∫ a, h a * max (w * a - P.continuationAtArrival w c (fun _ ↦ 0) u i) 0 ∂P.law i

lemma Instance.measurable_marginalScorePremium (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (h : ℝ → ℝ) (hh : Measurable h) : Measurable (P.marginalScorePremium w c i h) := by
  have hv : Measurable (fun v : (Fin n → ℝ) × ℝ ↦ P.continuationAtArrival w c (fun _ ↦ 0) v.1 i) :=
    P.measurable_continuationAtArrival hP hw hc (fun _ ↦ measurable_const)
      (fun j ↦ (measurable_pi_apply j).comp measurable_fst) i
  have hF : Measurable (fun v : (Fin n → ℝ) × ℝ ↦ h v.2 *
      max (w * v.2 - P.continuationAtArrival w c (fun _ ↦ 0) v.1 i) 0) :=
    (hh.comp measurable_snd).mul (((measurable_const.mul measurable_snd).sub hv).max measurable_const)
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

lemma Instance.abs_marginalScorePremium_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H)
    (i : Fin n) (h : ℝ → ℝ) (hb : ∀ᵐ a ∂P.law i, |h a| ≤ 1) (u : Fin n → ℝ) :
    |P.marginalScorePremium w c i h u| ≤ w * H := by
  have hv := P.continuationAtArrival_nonnegative hP hw.le hc (fun _ ↦ 0) u i
  have hn := norm_integral_le_of_norm_le_const (μ := P.law i)
    (f := fun a ↦ h a * max (w * a - P.continuationAtArrival w c (fun _ ↦ 0) u i) 0)
    (C := w * H) (by
      filter_upwards [hb, hbound i] with a ha hcap
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (show 0 ≤ max (w * a - P.continuationAtArrival w c (fun _ ↦ 0) u i) 0 from le_max_right _ _)]
      apply (mul_le_mul_of_nonneg_right ha (le_max_right _ _)).trans
      rw [one_mul]
      exact max_le ((sub_le_self _ hv).trans (mul_le_mul_of_nonneg_left hcap hw.le)) (mul_nonneg hw.le hH))
  simpa only [Instance.marginalScorePremium, Real.norm_eq_abs, probReal_univ, mul_one] using hn

noncomputable def Instance.reachedMarginalScorePremium (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (h : ℝ → ℝ) (ω : World n Unit) : ℝ :=
  if ω.2.1 i ≤ 1 ∧ (P.valuePolicy hP hw.le hc).rule.Reaches () ω.1 ω.2.1 i then
    P.marginalScorePremium w c i h ω.2.1 else 0

lemma Instance.reachedMarginalScorePremium_replaceValue (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (h : ℝ → ℝ) (ω : World n Unit) (a : ℝ) :
    P.reachedMarginalScorePremium hP hw hc i h (Function.update ω.1 i a, ω.2) =
      P.reachedMarginalScorePremium hP hw hc i h ω := by
  let π : Policy Unit n := (P.valuePolicy hP hw.le hc).rule
  change (if ω.2.1 i ≤ 1 ∧ π.Reaches () (Function.update ω.1 i a) ω.2.1 i then
      P.marginalScorePremium w c i h ω.2.1 else 0) =
    (if ω.2.1 i ≤ 1 ∧ π.Reaches () ω.1 ω.2.1 i then P.marginalScorePremium w c i h ω.2.1 else 0)
  by_cases ht : ω.2.1 i ≤ 1
  · simp only [ht, true_and, π.reaches_update_value () ω.1 ω.2.1 i a ht]
  · simp only [ht, false_and, if_false]

lemma Instance.measurable_reachedMarginalScorePremium (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin n) (h : ℝ → ℝ) (hh : Measurable h) :
    Measurable (P.reachedMarginalScorePremium hP hw hc i h) := by
  let π : Policy Unit n := (P.valuePolicy hP hw.le hc).rule
  have hπ : π.IsMeasurable := (P.valuePolicy hP hw.le hc).measurable_rule
  exact Measurable.ite ((measurableSet_le ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) measurable_const).inter
    (π.measurableSet_reaches hπ measurable_const (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
      (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i))
    ((P.measurable_marginalScorePremium hP hw hc i h hh).comp (measurable_fst.comp measurable_snd)) measurable_const

lemma Instance.integrable_reachedMarginalScorePremium (P Q : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H)
    (i : Fin n) (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ᵐ a ∂P.law i, |h a| ≤ 1) :
    Integrable (P.reachedMarginalScorePremium hP hw hc i h) (Q.worldLaw (Measure.dirac ())) := by
  apply Integrable.of_bound (P.measurable_reachedMarginalScorePremium hP hw hc i h hh).aestronglyMeasurable (w * H)
  exact Filter.Eventually.of_forall (fun ω ↦ by
    unfold Instance.reachedMarginalScorePremium
    split_ifs
    · rw [Real.norm_eq_abs]
      exact P.abs_marginalScorePremium_le hP hw hc hH hbound i h hb ω.2.1
    · simpa only [norm_zero] using mul_nonneg hw.le hH)

/-- Actual candidate conditioning identifies the reached score-premium mean
with the corresponding marginal pairing against `g_i`. -/
theorem Instance.mean_reachedMarginalScorePremium (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ a ∂P.law j, a ≤ H)
    (i : Fin n) (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ᵐ a ∂P.law i, |h a| ≤ 1) :
    (∫ ω : World n Unit, P.reachedMarginalScorePremium hP hw hc i h ω ∂P.worldLaw (Measure.dirac ())) =
      ∫ a, h a * P.marginalPremium hP hw hc i a ∂P.law i := by
  let π : Policy Unit n := (P.valuePolicy hP hw.le hc).rule
  let F := fun v : World n Unit × ℝ ↦ h v.2 * P.premiumAtValue hP hw hc i v
  have hF : Integrable F ((P.worldLaw (Measure.dirac ())).prod (P.law i)) :=
    (P.integrable_premiumAtValue_joint hP hw hc hH hbound i).bdd_mul
      ((hh.comp measurable_snd).aestronglyMeasurable)
      ((Measure.quasiMeasurePreserving_snd (μ := P.worldLaw (Measure.dirac ())) (ν := P.law i)).ae
        (by simpa only [Real.norm_eq_abs] using hb))
  apply Eq.symm
  calc
    _ = ∫ a, ∫ ω : World n Unit, F (ω, a) ∂P.worldLaw (Measure.dirac ()) ∂P.law i := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun a ↦ (integral_const_mul (h a) _).symm)
    _ = ∫ v : World n Unit × ℝ, F v ∂(P.worldLaw (Measure.dirac ())).prod (P.law i) :=
      (integral_prod_symm F hF).symm
    _ = ∫ ω : World n Unit, (∫ a, F (ω, a) ∂P.law i) ∂P.worldLaw (Measure.dirac ()) := integral_prod F hF
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [P.world_clocks_mem_unitInterval (Measure.dirac ())] with ω hω
      have he (a : ℝ) : P.premiumAtValue hP hw hc i (ω, a) =
          if π.Reaches () ω.1 ω.2.1 i then
            max (w * a - P.continuationAtArrival w c (fun _ ↦ 0) ω.2.1 i) 0 else 0 := by
        change (if π.Reaches () (Function.update ω.1 i a) ω.2.1 i then _ else 0) = _
        simp only [π.reaches_update_value () ω.1 ω.2.1 i a (hω i).2]
      by_cases hr : π.Reaches () ω.1 ω.2.1 i
      · change (∫ a, h a * P.premiumAtValue hP hw hc i (ω, a) ∂P.law i) =
          (if ω.2.1 i ≤ 1 ∧ π.Reaches () ω.1 ω.2.1 i then P.marginalScorePremium w c i h ω.2.1 else 0)
        rw [if_pos ⟨(hω i).2, hr⟩]
        unfold Instance.marginalScorePremium
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun a ↦ by dsimp only; rw [he, if_pos hr])
      · change (∫ a, h a * P.premiumAtValue hP hw hc i (ω, a) ∂P.law i) =
          (if ω.2.1 i ≤ 1 ∧ π.Reaches () ω.1 ω.2.1 i then P.marginalScorePremium w c i h ω.2.1 else 0)
        rw [if_neg (fun ht ↦ hr ht.2)]
        have hz : (fun a ↦ h a * P.premiumAtValue hP hw hc i (ω, a)) = (fun _ ↦ (0 : ℝ)) := by
          funext a
          rw [he, if_neg hr, mul_zero]
        rw [hz, integral_zero]

end ProphetSecretary.Model
