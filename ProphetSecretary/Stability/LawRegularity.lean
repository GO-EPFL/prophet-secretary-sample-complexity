import ProphetSecretary.Stability.WideLikelihoodEnvelope
import ProphetSecretary.Probability.WideFrozenTaylor
import ProphetSecretary.Model.LawRegret
import ProphetSecretary.Analysis.AbsoluteQuadraticSupport
import ProphetSecretary.Analysis.LipschitzSlopeAE

/-!
# Preliminary finite regularity under likelihood-law changes

The base optimizer is fixed when its payoff is differentiated. Exact Bellman
policy regret and the fixed-payoff Taylor bound give absolute quadratic affine
remainders. Constants here may depend on the finite number of distributions;
the universal law-curvature estimate is established separately.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

lemma RandomizedPolicy.likelihoodWide_envelope (π : RandomizedPolicy n) (P : Instance n)
    {w c H : ℝ} (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2))
    (hopt : π.scalarObjective (P.likelihoodWidePath h hh hb hm θ) w c =
      optimalScalarValue (P.likelihoodWidePath h hh hb hm θ) w c) :
    deriv (fun t ↦ π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c) θ =
      deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) θ := by
  have hV := P.hasDerivAt_optimalScalarValue_likelihoodWidePath hw hc hH hbound h hh hb hm hθ
  have hJ := π.hasDerivAt_scalarObjective_likelihoodWidePath P hw.le hc.le hH hbound h hh hb hm hθ
  have hmin : IsLocalMin (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c -
      π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c) θ := by
    exact Filter.Eventually.of_forall (fun t ↦ by
      change optimalScalarValue (P.likelihoodWidePath h hh hb hm θ) w c -
        π.scalarObjective (P.likelihoodWidePath h hh hb hm θ) w c ≤
          optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c - π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c
      rw [hopt, sub_self]
      exact sub_nonneg.mpr (scalarObjective_le_optimal π (P.likelihoodWidePath h hh hb hm t)
        ((P.likelihoodWidePath h hh hb hm t).integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm t hbound)) hw.le hc.le))
  have hz := hmin.hasDerivAt_eq_zero (hV.differentiableAt.hasDerivAt.sub hJ.differentiableAt.hasDerivAt)
  exact (sub_eq_zero.mp hz).symm

noncomputable def finiteLawScalarConstant (n : ℕ) (H w c : ℝ) : ℝ :=
  finiteLawRegretConstant n H w c + 32 * (w * H + c) * (n : ℝ)

/-- Absolute quadratic affine support over the wider open half interval. -/
theorem Instance.lawValue_quadraticGap (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    |optimalScalarValue (P.likelihoodWidePath h hh hb hm ρ) w c - optimalScalarValue (P.likelihoodWidePath h hh hb hm θ) w c -
      (ρ - θ) * deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) θ| ≤
        finiteLawScalarConstant n H w c * (ρ - θ) ^ 2 := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  let T := P.likelihoodWidePath h hh hb hm ρ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  have hT := T.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm ρ hbound)
  let C := Q.valuePolicy hQ hw.le hc.le
  have hOpt : C.scalarObjective Q w c = optimalScalarValue Q w c := Q.valuePolicy_optimal hQ hw hc.le
  have hDer := C.likelihoodWide_envelope P hw hc hH hbound h hh hb hm hθ hOpt
  have hFrozen := C.scalarObjective_likelihoodWidePath_taylor P hw.le hc.le hH hbound h hh hb hm hθ hρ
  rw [hDer] at hFrozen
  have hReg : optimalScalarValue T w c - C.scalarObjective T w c ≤ finiteLawRegretConstant n H w c * (ρ - θ) ^ 2 :=
    P.lawPolicy_regret_le hw hc hH hbound h hh hb hm hθ hρ
  have hReg0 : 0 ≤ optimalScalarValue T w c - C.scalarObjective T w c :=
    sub_nonneg.mpr (scalarObjective_le_optimal C T hT hw.le hc.le)
  have he : optimalScalarValue T w c - optimalScalarValue Q w c -
      (ρ - θ) * deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) θ =
      (optimalScalarValue T w c - C.scalarObjective T w c) +
      (C.scalarObjective T w c - C.scalarObjective Q w c -
        (ρ - θ) * deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) θ) := by
    rw [hOpt]
    ring
  change |optimalScalarValue T w c - optimalScalarValue Q w c -
    (ρ - θ) * deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) θ| ≤ _
  rw [he]
  calc
    _ ≤ |optimalScalarValue T w c - C.scalarObjective T w c| +
        |C.scalarObjective T w c - C.scalarObjective Q w c -
          (ρ - θ) * deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) θ| := abs_add_le _ _
    _ = (optimalScalarValue T w c - C.scalarObjective T w c) +
        |C.scalarObjective T w c - C.scalarObjective Q w c -
          (ρ - θ) * deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) θ| := by rw [abs_of_nonneg hReg0]
    _ ≤ finiteLawRegretConstant n H w c * (ρ - θ) ^ 2 + (32 * (w * H + c) * (n : ℝ)) * (ρ - θ) ^ 2 := add_le_add hReg hFrozen
    _ = _ := by unfold finiteLawScalarConstant; ring

/-- Preliminary finite Lipschitz derivative. The later curvature charge removes
its explicit dependence on the number of distributions. -/
theorem Instance.lawValue_deriv_lipschitz (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    |deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) ρ -
      deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) θ| ≤
        2 * finiteLawScalarConstant n H w c * |ρ - θ| :=
  ProphetSecretary.Analysis.abs_sub_slopes_le_of_absolute_quadratic
    (fun _x hx _y hy ↦ P.lawValue_quadraticGap hw hc hH hbound h hh hb hm hx hy) hθ hρ

/-- Concrete finite C^{1,1} data on an open interval containing the manuscript's
closed quarter interval. No optimized differentiability is assumed. -/
theorem Instance.lawValue_finite_C11 (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    (∀ θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2), DifferentiableAt ℝ (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) θ) ∧
      ∃ L : ℝ≥0, (L : ℝ) = 2 * finiteLawScalarConstant n H w c ∧
        LipschitzOnWith L (deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c)) (Ioo (-(1 / 2) : ℝ) (1 / 2)) := by
  refine ⟨fun θ hθ ↦ (P.hasDerivAt_optimalScalarValue_likelihoodWidePath hw hc hH hbound h hh hb hm hθ).differentiableAt, ?_⟩
  have hK : 0 ≤ 2 * finiteLawScalarConstant n H w c := by
    unfold finiteLawScalarConstant finiteLawRegretConstant
    positivity
  let L : ℝ≥0 := NNReal.mk (2 * finiteLawScalarConstant n H w c) hK
  refine ⟨L, rfl, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro θ hθ ρ hρ
  simpa only [L, Real.dist_eq, NNReal.coe_mk] using P.lawValue_deriv_lipschitz hw hc hH hbound h hh hb hm hρ hθ

theorem Instance.lawValue_secondDerivative_ae (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-(1 / 2) : ℝ) (1 / 2)),
      DifferentiableAt ℝ (deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c)) θ := by
  obtain ⟨L, _hL, hLip⟩ := (P.lawValue_finite_C11 hw hc hH hbound h hh hb hm).2
  exact ProphetSecretary.Analysis.lipschitzOn_ae_differentiableAt hLip

end ProphetSecretary.Model
