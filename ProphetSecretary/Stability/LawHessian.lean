import ProphetSecretary.Stability.LawRegularity
import ProphetSecretary.Model.LawAdaptationLimit
import ProphetSecretary.Model.LawKernelMean
import ProphetSecretary.Probability.WideFrozenInformationTaylor
import ProphetSecretary.Probability.WideFirstMoment
import ProphetSecretary.Analysis.BregmanSecond

/-! # Finite directional curvature under distributional perturbations
The second derivative is compared with the actual optimized-minus-frozen
adaptation limit. Only the frozen policy's Taylor remainder is differentiated;
its information bound and the state-kernel charge are independent of instance size.
-/
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

theorem Instance.lawValue_secondDerivative_bound_at (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2))
    (hD : DifferentiableAt ℝ (deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c)) θ)
    (hAdapt : let Q := P.likelihoodWidePath h hh hb hm θ
      let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
      let C := Q.valuePolicy hQ hw.le hc.le
      Tendsto (fun δ : ℝ ↦ (optimalScalarValue (P.likelihoodWidePath h hh hb hm (θ + δ)) w c -
        C.scalarObjective (P.likelihoodWidePath h hh hb hm (θ + δ)) w c) / δ ^ 2)
        (𝓝[≠] 0) (𝓝 (∑ i : Fin n, ∫ ω : World n Unit,
          (∑ A : Finset (Fin n), P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω) / 2
          ∂Q.worldLaw (Measure.dirac ())))) :
    |deriv (deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c)) θ| ≤
      8 * (w * H + c) * information P.law h +
        (4 * w ^ 2 * H * information P.law h / c) * (P.likelihoodWidePath h hh hb hm θ).totalFirstMoment := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let C := Q.valuePolicy hQ hw.le hc.le
  let f := fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c
  let L := ∑ i : Fin n, ∫ ω : World n Unit,
    (∑ A : Finset (Fin n), P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω) / 2
    ∂Q.worldLaw (Measure.dirac ())
  let B := 4 * (w * H + c) * information P.law h
  let K := 2 * w ^ 2 * H * information P.law h / c * Q.totalFirstMoment
  have hOpt : C.scalarObjective Q w c = f θ := Q.valuePolicy_optimal hQ hw hc.le
  have hEnv := C.likelihoodWide_envelope P hw hc hH hbound h hh hb hm hθ hOpt
  have hV := ProphetSecretary.Analysis.tendsto_bregman_quotient hθ
    (fun t ht ↦ (P.hasDerivAt_optimalScalarValue_likelihoodWidePath hw hc hH hbound h hh hb hm ht).differentiableAt.hasDerivAt)
    hD.hasDerivAt
  change Tendsto (fun δ : ℝ ↦ (f (θ + δ) - f θ - δ * deriv f θ) / δ ^ 2)
    (𝓝[≠] 0) (𝓝 (deriv (deriv f) θ / 2)) at hV
  change Tendsto (fun δ : ℝ ↦ (f (θ + δ) - C.scalarObjective (P.likelihoodWidePath h hh hb hm (θ + δ)) w c) / δ ^ 2)
    (𝓝[≠] 0) (𝓝 L) at hAdapt
  have hE : ∀ᶠ δ : ℝ in 𝓝[≠] 0,
      |(f (θ + δ) - f θ - δ * deriv f θ) / δ ^ 2 -
        (f (θ + δ) - C.scalarObjective (P.likelihoodWidePath h hh hb hm (θ + δ)) w c) / δ ^ 2| ≤ B := by
    have hAdd : Tendsto (fun δ : ℝ ↦ θ + δ) (𝓝 0) (𝓝 θ) := by
      have hC : Continuous (fun δ : ℝ ↦ θ + δ) := continuous_const.add continuous_id
      simpa only [add_zero] using hC.tendsto 0
    have hInside : ∀ᶠ δ : ℝ in 𝓝 0, θ + δ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := hAdd (Ioo_mem_nhds hθ.1 hθ.2)
    have hSmall : ∀ᶠ δ : ℝ in 𝓝 0, |δ| ≤ 1 / 8 := by
      filter_upwards [Icc_mem_nhds (by norm_num : -(1 / 8 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 8)] with δ hδ
      exact abs_le.mpr hδ
    filter_upwards [hInside.filter_mono nhdsWithin_le_nhds, hSmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with δ hNew hδ hne
    have hδne : δ ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
    have ht := C.scalarObjective_likelihoodWidePath_taylor_information P hw.le hc.le hH hbound h hh hb hm hθ hNew
      (by simpa only [add_sub_cancel_left] using hδ)
    rw [add_sub_cancel_left] at ht
    change |C.scalarObjective (P.likelihoodWidePath h hh hb hm (θ + δ)) w c - C.scalarObjective Q w c -
      δ * deriv (fun t ↦ C.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c) θ| ≤ B * δ ^ 2 at ht
    rw [hOpt, hEnv] at ht
    have hDiv : |(C.scalarObjective (P.likelihoodWidePath h hh hb hm (θ + δ)) w c - f θ - δ * deriv f θ) / δ ^ 2| ≤ B := by
      rw [abs_div, abs_of_nonneg (sq_nonneg δ)]
      exact (div_le_iff₀ (sq_pos_of_ne_zero hδne)).2 ht
    convert hDiv using 1
    congr 1
    ring
  have hBound : |deriv (deriv f) θ / 2 - L| ≤ B := le_of_tendsto (hV.sub hAdapt).abs hE
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun i _ ↦ integral_nonneg (fun ω ↦ div_nonneg
    (Finset.sum_nonneg (fun A _ ↦ P.lawAdaptationKernel_nonnegative hw hc hbound h hh hb hm θ i A ω)) (by norm_num)))
  have hLK : L ≤ K := P.mean_lawAdaptationKernel_le hw hc hH hbound h hh hb hm hθ
  have hFinal : |deriv (deriv f) θ| ≤ 2 * B + 2 * K := by
    obtain ⟨hLo, hHi⟩ := abs_le.mp hBound
    apply abs_le.mpr
    constructor <;> linarith
  convert hFinal using 1
  dsimp only [B, K]
  ring


/-- The finite directional Hessian bound in `upfish:curvature`. All exceptional
sets are discharged; the coefficient is independent of instance cardinality. -/
theorem Instance.lawValue_secondDerivative_bound_ae (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-(1 / 4) : ℝ) (1 / 4)),
      |deriv (deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c)) θ| ≤
        (8 * (w * H + c) + 6 * w ^ 2 * H * P.totalFirstMoment / c) * information P.law h := by
  have hSub : Ioo (-(1 / 4) : ℝ) (1 / 4) ⊆ Ioo (-(1 / 2) : ℝ) (1 / 2) := by
    intro θ hθ
    constructor <;> linarith [hθ.1, hθ.2]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hSub
      (P.lawValue_secondDerivative_ae hw hc hH hbound h hh hb hm),
    P.lawAdaptationRegret_kernel_limit_ae hw hc hH hbound h hh hb hm,
    ae_restrict_mem measurableSet_Ioo] with θ hD hA hθ
  have hHalf := hSub hθ
  have hBound := P.lawValue_secondDerivative_bound_at hw hc hH hbound h hh hb hm hHalf hD hA
  have hMoment := P.totalFirstMoment_likelihoodWidePath_le
    (P.integrable_maximum_of_bounded hbound) h hh hb hm (abs_le.mpr ⟨hHalf.1.le, hHalf.2.le⟩)
  have hInfo := information_nonnegative P.law h
  have hCoef : 0 ≤ 4 * w ^ 2 * H * information P.law h / c := by positivity
  apply hBound.trans
  calc
    _ ≤ 8 * (w * H + c) * information P.law h +
        (4 * w ^ 2 * H * information P.law h / c) * ((3 / 2 : ℝ) * P.totalFirstMoment) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hMoment hCoef)
    _ = _ := by ring

end ProphetSecretary.Model
