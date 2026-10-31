import ProphetSecretary.Model.ClockConditionalBellmanLoss
import ProphetSecretary.Model.LawRegret

/-!
# Residual-uniform clock domination for law adaptation

Only the candidate clock is integrated. All offers, other clocks and the old
policy seed are fixed. The quadratic bound is independent of those residual
coordinates and is used solely for finite-instance dominated convergence.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

noncomputable def Instance.lawConditionalRegret (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (i : Fin n) (ω : World n Unit) : ℝ :=
  let Q := P.likelihoodWidePath h hh hb hm θ
  let T := P.likelihoodWidePath h hh hb hm ρ
  let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  (Q.valuePolicy hQ hw.le hc).rule.clockConditionalBellmanLoss T w c i ω

lemma Instance.lawConditionalRegret_nonnegative (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (i : Fin n) (ω : World n Unit) : 0 ≤ P.lawConditionalRegret hw hc hbound h hh hb hm θ ρ i ω :=
  Policy.clockConditionalBellmanLoss_nonnegative _ _ _ _ _ _

lemma Instance.measurable_lawConditionalRegret (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (i : Fin n) : Measurable (P.lawConditionalRegret hw hc hbound h hh hb hm θ ρ i) := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  let T := P.likelihoodWidePath h hh hb hm ρ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  have hT := T.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm ρ hbound)
  exact (Q.valuePolicy hQ hw.le hc).rule.measurable_clockConditionalBellmanLoss
    (Q.valuePolicy hQ hw.le hc).measurable_rule T hT hw hc i

/-- Pointwise clock band bound, before any residual data is averaged. -/
lemma Instance.lawClockLoss_le_band (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2))
    (i : Fin n) (ω : World n Unit) {t : ℝ} (ht : 0 ≤ t) :
    let Q := P.likelihoodWidePath h hh hb hm θ
    let T := P.likelihoodWidePath h hh hb hm ρ
    let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
    let D := (2 * (w * H + c) * (n : ℝ)) * |ρ - θ|
    (Q.valuePolicy hQ hw.le hc).rule.reachedArrivalBellmanLoss T w c i (Instance.replaceClock i (ω, t)) ≤
      if |T.candidateGap w c i (ω.1 i) ω.2.1 t| ≤ D then D else 0 := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  let T := P.likelihoodWidePath h hh hb hm ρ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let π : Policy Unit n := (Q.valuePolicy hQ hw.le hc).rule
  let D := (2 * (w * H + c) * (n : ℝ)) * |ρ - θ|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbnd := P.lawPolicy_localLoss_le_band hw hc hH hbound h hh hb hm hθ hρ ω.1 (Function.update ω.2.1 i t) i
    (by simpa only [Function.update_self] using ht)
  change π.arrivalBellmanLoss T w c () ω.1 (Function.update ω.2.1 i t) i ≤
    if |w * ω.1 i - T.continuationAtArrival w c ω.1 (Function.update ω.2.1 i t) i| ≤ D then D else 0 at hbnd
  rw [← T.candidateGap_eq_replacedAcceptanceGap w c i ω.1 ω.2.1 t] at hbnd
  change (if π.Reaches () ω.1 (Function.update ω.2.1 i t) i then
    π.arrivalBellmanLoss T w c () ω.1 (Function.update ω.2.1 i t) i else 0) ≤
      if |T.candidateGap w c i (ω.1 i) ω.2.1 t| ≤ D then D else 0
  by_cases hr : π.Reaches () ω.1 (Function.update ω.2.1 i t) i
  · rw [if_pos hr]
    exact hbnd
  · rw [if_neg hr]
    split_ifs
    · exact hD
    · exact le_rfl

/-- The entire candidate-clock conditional regret has an explicit quadratic
bound that holds for every residual vector, including null-model vectors. -/
theorem Instance.lawConditionalRegret_le (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2))
    (i : Fin n) (ω : World n Unit) :
    P.lawConditionalRegret hw hc.le hbound h hh hb hm θ ρ i ω ≤
      8 * (1 + (n : ℝ)) * (2 * (w * H + c) * (n : ℝ)) ^ 2 * (ρ - θ) ^ 2 / c := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  let T := P.likelihoodWidePath h hh hb hm ρ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  have hT := T.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm ρ hbound)
  let π : Policy Unit n := (Q.valuePolicy hQ hw.le hc.le).rule
  let D := (2 * (w * H + c) * (n : ℝ)) * |ρ - θ|
  let g := T.candidateGap w c i (ω.1 i) ω.2.1
  let E := ProphetSecretary.Analysis.thresholdBand g D
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : MeasurableSet E := ProphetSecretary.Analysis.measurableSet_thresholdBand (T.measurable_candidateGap hT hw.le hc.le i (ω.1 i) ω.2.1) D
  let f := fun t : ℝ ↦ π.reachedArrivalBellmanLoss T w c i (Instance.replaceClock i (ω, t))
  have hfm : Measurable f :=
    ((π.measurable_reachedArrivalBellmanLoss (Q.valuePolicy hQ hw.le hc.le).measurable_rule T hT hw hc.le i).comp
      (measurable_clockReplacement i)).comp (measurable_const.prodMk measurable_id)
  have hBand : ∀ᵐ t : ℝ ∂Instance.uniformClock, f t ≤ E.indicator (fun _ ↦ D) t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hbnd := P.lawClockLoss_le_band hw hc.le hH hbound h hh hb hm hθ hρ i ω ht.1
    change f t ≤ if |g t| ≤ D then D else 0 at hbnd
    by_cases he : t ∈ E
    · rw [Set.indicator_of_mem (s := E) he]
      have he' : |g t| ≤ D := he.2
      simpa only [if_pos he'] using hbnd
    · rw [Set.indicator_of_notMem (s := E) he]
      have he' : ¬ |g t| ≤ D := fun hgt ↦ he ⟨ht, hgt⟩
      simpa only [if_neg he'] using hbnd
  have hfi : Integrable f Instance.uniformClock := by
    apply Integrable.of_bound hfm.aestronglyMeasurable D
    filter_upwards [hBand] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (π.reachedArrivalBellmanLoss_nonnegative T w c i (Instance.replaceClock i (ω, t)))]
    apply ht.trans
    by_cases he : t ∈ E
    · rw [Set.indicator_of_mem (s := E) he]
    · rw [Set.indicator_of_notMem (s := E) he]
      exact hD
  have hbnd := integral_mono_ae hfi ((integrable_const D).indicator hE) hBand
  rw [integral_indicator_const _ hE, smul_eq_mul] at hbnd
  have heq : Instance.uniformClock.real E = volume.real E := by
    unfold Instance.uniformClock Measure.real
    rw [Measure.restrict_apply hE, inter_eq_left.mpr (fun _ ht ↦ ht.1)]
  rw [heq] at hbnd
  have hvol := T.candidateGap_band_volume hT hw hc hD i (ω.1 i) ω.2.1
  change (∫ t : ℝ, f t ∂Instance.uniformClock) ≤ _
  calc
    _ ≤ volume.real E * D := hbnd
    _ ≤ (2 * D / (c / (4 * (1 + (n : ℝ))))) * D := mul_le_mul_of_nonneg_right hvol hD
    _ = _ := by
      dsimp only [D]
      rw [← sq_abs (ρ - θ)]
      field_simp [hc.ne', (show (4 : ℝ) * (1 + (n : ℝ)) ≠ 0 by positivity)]
      ring

/-- A common residual-data bound for the normalized quotient near the base
parameter. This is the finite dominating function used in the Hessian limit. -/
theorem Instance.eventually_lawConditionalRegret_bound (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    ∀ᶠ δ : ℝ in 𝓝[≠] 0, ∀ (i : Fin n) (ω : World n Unit),
      |P.lawConditionalRegret hw hc.le hbound h hh hb hm θ (θ + δ) i ω / δ ^ 2| ≤
        8 * (1 + (n : ℝ)) * (2 * (w * H + c) * (n : ℝ)) ^ 2 / c := by
  have hcont : Continuous (fun δ : ℝ ↦ θ + δ) := continuous_const.add continuous_id
  have hAdd : Tendsto (fun δ : ℝ ↦ θ + δ) (𝓝 0) (𝓝 θ) := by simpa only [add_zero] using hcont.tendsto 0
  have hInside : ∀ᶠ δ : ℝ in 𝓝 0, θ + δ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := hAdd (Ioo_mem_nhds hθ.1 hθ.2)
  filter_upwards [hInside.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with δ hδ hne i ω
  have hδne : δ ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
  have hNon := div_nonneg (P.lawConditionalRegret_nonnegative hw hc.le hbound h hh hb hm θ (θ + δ) i ω) (sq_nonneg δ)
  rw [abs_of_nonneg hNon]
  have hB := P.lawConditionalRegret_le hw hc hH hbound h hh hb hm hθ hδ i ω
  rw [add_sub_cancel_left] at hB
  have hDiv := div_le_div_of_nonneg_right hB (sq_nonneg δ)
  apply hDiv.trans_eq
  field_simp [hc.ne', hδne]

end ProphetSecretary.Model
