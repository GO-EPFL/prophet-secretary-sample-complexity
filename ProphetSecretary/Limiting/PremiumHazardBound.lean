import ProphetSecretary.Limiting.PremiumTailResidual

/-!
# A sharp bound for adaptive stopped premium drift

The continuation value may depend measurably on the full clock vector. The
pointwise tail estimate is uniform in that value, so no independence from the
stopping event or the unseen set is assumed. This supplies the analytic drift
bound used in the causal Poisson comparison.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {N : ℕ}

noncomputable def integratedTailHazard (P : Model.Instance N) (H : ℝ)
    (z : ℝ × (Fin N → ℝ)) : ℝ :=
  ∫ x in Icc 0 H, |tailHazardError (distributionTail P x) z.1 z.2|

lemma measurable_integratedTailHazard (P : Model.Instance N) (H : ℝ) :
    Measurable (integratedTailHazard P H) :=
  (measurable_tailHazardIntegrand P).stronglyMeasurable.integral_prod_left'.measurable

lemma integrable_integratedTailHazard (P : Model.Instance N) (H : ℝ) :
    Integrable (integratedTailHazard P H)
      (Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)) :=
  (integrable_tailHazardIntegrand P H).integral_prod_right

lemma integral_integratedTailHazard_le (P : Model.Instance N) {H : ℝ} (hH : 0 ≤ H) :
    (∫ z, integratedTailHazard P H z ∂Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)) ≤
      (Real.pi / 2) * H * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) := by
  change (∫ z, (∫ x, tailHazardIntegrand P (x,z) ∂volume.restrict (Icc 0 H))
    ∂Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)) ≤ _
  rw [← integral_prod_symm _ (integrable_tailHazardIntegrand P H)]
  exact integral_tailHazardIntegrand_sharp_le P hH

lemma measurable_premiumHazardError (P : Model.Instance N) {H w : ℝ}
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (v : ℝ × (Fin N → ℝ) → ℝ) (hv : Measurable v) :
    Measurable (fun z => premiumHazardError P w (v z) z.1 z.2) := by
  have hP := P.integrable_maximum_of_bounded hcap
  have hm (i : Fin N) : Measurable (fun z => Model.positivePremium (P.law i) w (v z)) :=
    ((Model.positivePremium_continuous (P.law i) (P.integrable_maximum_iff.mp hP i) w).measurable).comp hv
  have hs : Measurable (fun z : ℝ × (Fin N → ℝ) =>
      ∑ i, if z.1 < z.2 i then Model.positivePremium (P.law i) w (v z) else 0) := by
    apply Finset.measurable_fun_sum
    intro i _
    exact Measurable.ite (measurableSet_lt measurable_fst ((measurable_pi_apply i).comp measurable_snd))
      (hm i) measurable_const
  have hsum : Measurable (fun z => ∑ i, Model.positivePremium (P.law i) w (v z)) :=
    Finset.measurable_fun_sum _ (fun i _ => hm i)
  exact (hs.div (measurable_const.sub measurable_fst)).sub hsum

lemma integrable_adaptive_premiumHazardError (P : Model.Instance N) {H w : ℝ}
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hw : 0 < w)
    (v : ℝ × (Fin N → ℝ) → ℝ) (hv : Measurable v) (hv0 : ∀ z, 0 ≤ v z) :
    Integrable (fun z => premiumHazardError P w (v z) z.1 z.2)
      (Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)) := by
  apply ((integrable_integratedTailHazard P H).const_mul w).mono'
    (measurable_premiumHazardError P hcap v hv).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]
    exact premiumHazardError_abs_le P hcap hw (hv0 z) z.1 z.2

/-- The sharp drift estimate remains valid after a measurable stopping event
is imposed and its indicator is then dropped inside the absolute bound. -/
theorem stopped_premiumHazardError_integral_abs_le (P : Model.Instance N) {H w : ℝ}
    (hH : 0 ≤ H) (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hw : 0 < w)
    (v : ℝ × (Fin N → ℝ) → ℝ) (hv : Measurable v) (hv0 : ∀ z, 0 ≤ v z)
    (E : Set (ℝ × (Fin N → ℝ))) (hE : MeasurableSet E) :
    |∫ z, E.indicator (fun z => premiumHazardError P w (v z) z.1 z.2) z
      ∂Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)| ≤
      (Real.pi / 2) * w * H * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) := by
  let F := fun z : ℝ × (Fin N → ℝ) => premiumHazardError P w (v z) z.1 z.2
  let μ := Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)
  have hi : Integrable F μ := integrable_adaptive_premiumHazardError P hcap hw v hv hv0
  have hdom := integral_mono (hi.indicator hE).abs ((integrable_integratedTailHazard P H).const_mul w)
    (fun z => by
      change |E.indicator F z| ≤ w * integratedTailHazard P H z
      by_cases hz : z ∈ E
      · rw [Set.indicator_of_mem hz]
        exact premiumHazardError_abs_le P hcap hw (hv0 z) z.1 z.2
      · rw [Set.indicator_of_notMem hz, abs_zero]
        exact mul_nonneg hw.le (integral_nonneg fun _ => abs_nonneg _))
  rw [integral_const_mul] at hdom
  have hbound := mul_le_mul_of_nonneg_left (integral_integratedTailHazard_le P hH) hw.le
  have h := (abs_integral_le_integral_abs (f := E.indicator F)).trans hdom |>.trans hbound
  exact h.trans_eq (by ring)

lemma measurable_premiumHazardErrorBy {Ω : Type*} [MeasurableSpace Ω]
    (P : Model.Instance N) {H w : ℝ} (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (v t : Ω → ℝ) (u : Ω → Fin N → ℝ) (hv : Measurable v) (ht : Measurable t)
    (hu : ∀ i, Measurable (fun q => u q i)) :
    Measurable (fun q => premiumHazardError P w (v q) (t q) (u q)) := by
  have hP := P.integrable_maximum_of_bounded hcap
  have hm (i : Fin N) : Measurable (fun q => Model.positivePremium (P.law i) w (v q)) :=
    ((Model.positivePremium_continuous (P.law i) (P.integrable_maximum_iff.mp hP i) w).measurable).comp hv
  have hs : Measurable (fun q => ∑ i, if t q < u q i then Model.positivePremium (P.law i) w (v q) else 0) := by
    apply Finset.measurable_fun_sum
    intro i _
    exact Measurable.ite (measurableSet_lt ht (hu i)) (hm i) measurable_const
  have hsum : Measurable (fun q => ∑ i, Model.positivePremium (P.law i) w (v q)) :=
    Finset.measurable_fun_sum _ (fun i _ => hm i)
  exact (hs.div (measurable_const.sub ht)).sub hsum

/-- Independent auxiliary data can include offer values and policy randomness.
The stopping event may use these inputs and the clocks jointly. -/
theorem stopped_premiumHazardError_product_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Model.Instance N) {H w : ℝ}
    (hH : 0 ≤ H) (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hw : 0 < w)
    (v : Ω × (ℝ × (Fin N → ℝ)) → ℝ) (hv : Measurable v) (hv0 : ∀ q, 0 ≤ v q)
    (E : Set (Ω × (ℝ × (Fin N → ℝ)))) (hE : MeasurableSet E) :
    |∫ q, E.indicator (fun q => premiumHazardError P w (v q) q.2.1 q.2.2) q
      ∂μ.prod (Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N))| ≤
      (Real.pi / 2) * w * H * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) := by
  let ν := Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)
  let F := fun q : Ω × (ℝ × (Fin N → ℝ)) => premiumHazardError P w (v q) q.2.1 q.2.2
  have hG : Integrable (fun q : Ω × (ℝ × (Fin N → ℝ)) => w * integratedTailHazard P H q.2) (μ.prod ν) :=
    ((integrable_integratedTailHazard P H).const_mul w).comp_snd μ
  have hFm : Measurable F := measurable_premiumHazardErrorBy P hcap v
    (fun q => q.2.1) (fun q => q.2.2) hv (measurable_fst.comp measurable_snd)
    (fun i => (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))
  have hi : Integrable F (μ.prod ν) := by
    apply hG.mono' hFm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]
      exact premiumHazardError_abs_le P hcap hw (hv0 q) q.2.1 q.2.2
  have hdom := integral_mono (hi.indicator hE).abs hG (fun q => by
    change |E.indicator F q| ≤ w * integratedTailHazard P H q.2
    by_cases hq : q ∈ E
    · rw [Set.indicator_of_mem hq]
      exact premiumHazardError_abs_le P hcap hw (hv0 q) q.2.1 q.2.2
    · rw [Set.indicator_of_notMem hq, abs_zero]
      exact mul_nonneg hw.le (integral_nonneg fun _ => abs_nonneg _))
  have heq : (∫ q : Ω × (ℝ × (Fin N → ℝ)), w * integratedTailHazard P H q.2 ∂μ.prod ν) =
      w * ∫ z, integratedTailHazard P H z ∂ν := by
    simpa only [probReal_univ, one_smul, integral_const_mul] using
      (integral_fun_snd (μ := μ) (ν := ν) (fun z : ℝ × (Fin N → ℝ) => w * integratedTailHazard P H z))
  rw [heq] at hdom
  have hb := mul_le_mul_of_nonneg_left (integral_integratedTailHazard_le P hH) hw.le
  have h := ((abs_integral_le_integral_abs (f := E.indicator F)).trans hdom).trans hb
  exact h.trans_eq (by ring)

/-- A clock marginal suffices: the continuation and stopping event may use
additional observations not recoverable from the projected clocks. Actual
hybrid projections establish this marginal by a separate product-law proof. -/
theorem stopped_premiumHazardError_marginal_bound {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (P : Model.Instance N) {H w : ℝ}
    (hH : 0 ≤ H) (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hw : 0 < w)
    (T : Ω → ℝ) (U : Ω → Fin N → ℝ)
    (hTU : MeasurePreserving (fun q => (T q,U q)) ρ
      (Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)))
    (v : Ω → ℝ) (hv : Measurable v) (hv0 : ∀ q, 0 ≤ v q)
    (E : Set Ω) (hE : MeasurableSet E) :
    |∫ q, E.indicator (fun q => premiumHazardError P w (v q) (T q) (U q)) q ∂ρ| ≤
      (Real.pi / 2) * w * H * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) := by
  let ν := Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)
  let F := fun q : Ω => premiumHazardError P w (v q) (T q) (U q)
  have hG : Integrable (fun q : Ω => w * integratedTailHazard P H (T q,U q)) ρ :=
    hTU.integrable_comp_of_integrable ((integrable_integratedTailHazard P H).const_mul w)
  have hFm : Measurable F := measurable_premiumHazardErrorBy P hcap v T U hv
    (measurable_fst.comp hTU.measurable)
    (fun i => (measurable_pi_apply i).comp (measurable_snd.comp hTU.measurable))
  have hi : Integrable F ρ := by
    apply hG.mono' hFm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]
      exact premiumHazardError_abs_le P hcap hw (hv0 q) (T q) (U q)
  have hdom := integral_mono (hi.indicator hE).abs hG (fun q => by
    change |E.indicator F q| ≤ w * integratedTailHazard P H (T q,U q)
    by_cases hq : q ∈ E
    · rw [Set.indicator_of_mem hq]
      exact premiumHazardError_abs_le P hcap hw (hv0 q) (T q) (U q)
    · rw [Set.indicator_of_notMem hq, abs_zero]
      exact mul_nonneg hw.le (integral_nonneg fun _ => abs_nonneg _))
  have heq : (∫ q, w * integratedTailHazard P H (T q,U q) ∂ρ) =
      w * ∫ z, integratedTailHazard P H z ∂ν := by
    have he := integral_map (μ := ρ) hTU.measurable.aemeasurable
      ((measurable_integratedTailHazard P H).const_mul w).aestronglyMeasurable
    rw [hTU.map_eq, integral_const_mul] at he
    exact he.symm
  rw [heq] at hdom
  have hb := mul_le_mul_of_nonneg_left (integral_integratedTailHazard_le P hH) hw.le
  exact (((abs_integral_le_integral_abs (f := E.indicator F)).trans hdom).trans hb).trans_eq (by ring)

end ProphetSecretary.Limiting
