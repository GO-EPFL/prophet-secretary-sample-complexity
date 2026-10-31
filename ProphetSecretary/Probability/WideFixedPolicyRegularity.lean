import ProphetSecretary.Probability.WideFrozenInformationTaylor
import ProphetSecretary.Analysis.AbsoluteQuadraticSupport
import ProphetSecretary.Analysis.LipschitzSlopeAE
import ProphetSecretary.Analysis.BregmanSecond
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # Dimension-free curvature for every fixed online policy
The policy and its independent seed law remain fixed throughout the curve.
A preliminary finite estimate supplies absolute continuity; the product-score
Taylor estimate improves the integrated curvature to its information scale.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

lemma RandomizedPolicy.fixedLaw_deriv_finite_lipschitz (π : RandomizedPolicy n) (P : Instance n)
    {w c H : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    ∃ L : ℝ≥0, LipschitzOnWith L (deriv (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c))
      (Ioo (-(1 / 2) : ℝ) (1 / 2)) := by
  refine ⟨NNReal.mk (64 * (w * H + c) * (n : ℝ)) (by positivity), ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro θ hθ ρ hρ
  have hB := ProphetSecretary.Analysis.abs_sub_slopes_le_of_absolute_quadratic
    (fun x hx y hy ↦ π.scalarObjective_likelihoodWidePath_taylor P hw hc hH hbound h hh hb hm hx hy) hρ hθ
  simp only [Real.dist_eq, NNReal.coe_mk]
  convert hB using 1
  ring

theorem RandomizedPolicy.fixedLaw_secondDerivative_bound_ae (π : RandomizedPolicy n) (P : Instance n)
    {w c H : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-(1 / 4) : ℝ) (1 / 4)),
      |deriv (deriv (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c)) θ| ≤
        8 * (w * H + c) * information P.law h := by
  let f := fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c
  obtain ⟨L, hLip⟩ := π.fixedLaw_deriv_finite_lipschitz P hw hc hH hbound h hh hb hm
  have hSub : Ioo (-(1 / 4) : ℝ) (1 / 4) ⊆ Ioo (-(1 / 2) : ℝ) (1 / 2) := by
    intro θ hθ; constructor <;> linarith [hθ.1, hθ.2]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hSub
      (ProphetSecretary.Analysis.lipschitzOn_ae_differentiableAt hLip), ae_restrict_mem measurableSet_Ioo] with θ hD hθ
  have hHalf := hSub hθ
  have hLimit := ProphetSecretary.Analysis.tendsto_bregman_quotient hHalf
    (fun t ht ↦ (π.hasDerivAt_scalarObjective_likelihoodWidePath P hw hc hH hbound h hh hb hm ht).differentiableAt.hasDerivAt)
    hD.hasDerivAt
  have hE : ∀ᶠ δ : ℝ in 𝓝[≠] 0,
      |(f (θ + δ) - f θ - δ * deriv f θ) / δ ^ 2| ≤ 4 * (w * H + c) * information P.law h := by
    have hAdd : Tendsto (fun δ : ℝ ↦ θ + δ) (𝓝 0) (𝓝 θ) := by
      have hC : Continuous (fun δ : ℝ ↦ θ + δ) := continuous_const.add continuous_id
      simpa only [add_zero] using hC.tendsto 0
    have hInside : ∀ᶠ δ : ℝ in 𝓝 0, θ + δ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := hAdd (Ioo_mem_nhds hHalf.1 hHalf.2)
    have hSmall : ∀ᶠ δ : ℝ in 𝓝 0, |δ| ≤ 1 / 8 := by
      filter_upwards [Icc_mem_nhds (by norm_num : -(1 / 8 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 8)] with δ ht
      exact abs_le.mpr ht
    filter_upwards [hInside.filter_mono nhdsWithin_le_nhds, hSmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with δ hNew hδ hne
    have hδne : δ ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
    have hB := π.scalarObjective_likelihoodWidePath_taylor_information P hw hc hH hbound h hh hb hm hHalf hNew
      (by simpa only [add_sub_cancel_left] using hδ)
    rw [add_sub_cancel_left] at hB
    rw [abs_div, abs_of_nonneg (sq_nonneg δ)]
    exact (div_le_iff₀ (sq_pos_of_ne_zero hδne)).2 hB
  have hB := le_of_tendsto hLimit.abs hE
  change |deriv (deriv f) θ / 2| ≤ 4 * (w * H + c) * information P.law h at hB
  rw [abs_div] at hB
  norm_num at hB
  change |deriv (deriv f) θ| ≤ _
  linarith

theorem RandomizedPolicy.fixedLaw_deriv_lipschitz_information (π : RandomizedPolicy n) (P : Instance n)
    {w c H : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) (hρ : ρ ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    |deriv (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c) ρ -
      deriv (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c) θ| ≤
        (8 * (w * H + c) * information P.law h) * |ρ - θ| := by
  let f := fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c
  let g := deriv f
  have hQuarter : uIcc θ ρ ⊆ Icc (-(1 / 4) : ℝ) (1 / 4) := by
    intro t ht
    exact ⟨(le_min hθ.1 hρ.1).trans ht.1, ht.2.trans (max_le hθ.2 hρ.2)⟩
  obtain ⟨L, hLip⟩ := π.fixedLaw_deriv_finite_lipschitz P hw hc hH hbound h hh hb hm
  have hAC : AbsolutelyContinuousOnInterval g θ ρ := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := L)
    apply hLip.mono
    intro t ht
    have hq := hQuarter ht
    constructor <;> linarith [hq.1, hq.2]
  have hGlobal := (ae_restrict_iff' measurableSet_Ioo).mp
    (π.fixedLaw_secondDerivative_bound_ae P hw hc hH hbound h hh hb hm)
  have hBound : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc θ ρ → ‖deriv g t‖ ≤ 8 * (w * H + c) * information P.law h := by
    filter_upwards [hGlobal, volume.ae_ne (-(1 / 4) : ℝ), volume.ae_ne (1 / 4 : ℝ)] with t ht hL hR
    intro htu
    have hq := hQuarter (uIoc_subset_uIcc htu)
    have hi : t ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) :=
      ⟨lt_of_le_of_ne hq.1 (Ne.symm hL), lt_of_le_of_ne hq.2 hR⟩
    simpa only [Real.norm_eq_abs] using ht hi
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const_ae hBound
  rw [hAC.integral_deriv_eq_sub] at hI
  simpa only [Real.norm_eq_abs] using hI

end ProphetSecretary.Model
