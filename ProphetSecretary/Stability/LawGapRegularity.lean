import ProphetSecretary.Stability.LawCurvature
import ProphetSecretary.Model.CompetitiveBasic

/-! # Distributional regularity of the normalized scalar gap
The global competitive constant is held fixed. The optimized instance value
and the prophet benchmark are differentiated as distinct functions.
-/
open MeasureTheory Set
open scoped Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability ProphetSecretary.Analysis
variable {n : ℕ}

lemma Instance.deriv_normalizedScalarGap_likelihoodWidePath (P : Instance n) {H lam : ℝ}
    (hH : 0 ≤ H) (hlam : lam ∈ Ioo (0 : ℝ) 1) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    deriv (fun t ↦ normalizedScalarGap (P.likelihoodWidePath h hh hb hm t) lam) θ =
      deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) lam (1 - lam)) θ -
        (optimalCompetitiveRatio * lam) * deriv (fun t ↦ (P.likelihoodWidePath h hh hb hm t).expectedMaximum) θ := by
  have hHalf : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := by constructor <;> linarith [hθ.1, hθ.2]
  have hV := (P.hasDerivAt_optimalScalarValue_likelihoodWidePath hlam.1 (sub_pos.mpr hlam.2) hH hbound h hh hb hm hHalf).differentiableAt.hasDerivAt
  have hM := (P.expectedMaximum_likelihoodWidePath_twice_differentiable hH hbound h hh hb hm hHalf).1.hasDerivAt
  have hD := hV.sub (((hM.const_mul lam).add_const (1 - lam)).const_mul optimalCompetitiveRatio)
  have hD' : HasDerivAt (fun t ↦ normalizedScalarGap (P.likelihoodWidePath h hh hb hm t) lam)
      (deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) lam (1 - lam)) θ -
        (optimalCompetitiveRatio * lam) * deriv (fun t ↦ (P.likelihoodWidePath h hh hb hm t).expectedMaximum) θ) θ := by
    convert hD using 1
    all_goals first | rfl | ring
  exact hD'.deriv

theorem Instance.lawGap_deriv_lipschitz_uniform (P : Instance n) {H δ lam : ℝ}
    (hH : 0 ≤ H) (hδ : 0 < δ) (hlam : lam ∈ Icc δ (1 - δ))
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) (hρ : ρ ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    |deriv (fun t ↦ normalizedScalarGap (P.likelihoodWidePath h hh hb hm t) lam) ρ -
      deriv (fun t ↦ normalizedScalarGap (P.likelihoodWidePath h hh hb hm t) lam) θ| ≤
      ((lawCurvatureConstant H δ + 8 * H) * (1 + P.totalFirstMoment) * information P.law h) * |ρ - θ| := by
  have hlam' : lam ∈ Ioo (0 : ℝ) 1 := ⟨hδ.trans_le hlam.1, by linarith [hlam.2]⟩
  rw [P.deriv_normalizedScalarGap_likelihoodWidePath hH hlam' hbound h hh hb hm hρ,
    P.deriv_normalizedScalarGap_likelihoodWidePath hH hlam' hbound h hh hb hm hθ]
  let a := optimalCompetitiveRatio * lam
  have ha0 : 0 ≤ a := mul_nonneg optimalCompetitiveRatio_nonnegative hlam'.1.le
  have ha1 : a ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right optimalCompetitiveRatio_le_one hlam'.1.le).trans
      (by simpa only [one_mul] using hlam'.2.le)
  let f := fun t ↦ deriv (fun s ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm s) lam (1 - lam)) t
  let g := fun t ↦ deriv (fun s ↦ (P.likelihoodWidePath h hh hb hm s).expectedMaximum) t
  have hTriangle : |(f ρ - a * g ρ) - (f θ - a * g θ)| ≤ |f ρ - f θ| + |g ρ - g θ| := by
    have he : (f ρ - a * g ρ) - (f θ - a * g θ) = (f ρ - f θ) - a * (g ρ - g θ) := by ring
    rw [he]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_of_nonneg ha0]
    exact add_le_add le_rfl (mul_le_of_le_one_left (abs_nonneg _) ha1)
  have hV := P.lawScalarUnit_deriv_lipschitz_uniform hH hδ hlam hbound h hh hb hm hθ hρ
  have hM := P.expectedMaximum_likelihoodWidePath_deriv_lipschitz hH hbound h hh hb hm hθ hρ
  have hS := P.totalFirstMoment_nonnegative
  have hI := information_nonnegative P.law h
  change |(f ρ - a * g ρ) - (f θ - a * g θ)| ≤ _
  apply hTriangle.trans ((add_le_add hV hM).trans ?_)
  have hExtra : 0 ≤ (8 * H * P.totalFirstMoment * information P.law h) * |ρ - θ| := by positivity
  nlinarith

end ProphetSecretary.Model
