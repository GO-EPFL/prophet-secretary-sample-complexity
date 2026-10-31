import ProphetSecretary.Stability.LawGapRegularity
import ProphetSecretary.Model.MidpointRegret

/-!
# Curvature of the regret of a fixed competing policy

The optimized scalar value and the fixed-policy payoff are differentiated
separately along the actual wider likelihood path. Their derivative difference
has a common information-scale Lipschitz bound, uniform in the policy and n.
-/
open MeasureTheory Set
open scoped Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability ProphetSecretary.Analysis
variable {n : ℕ}

lemma Instance.likelihoodWidePath_zero_eq (P : Instance n)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    P.likelihoodWidePath h hh hb hm 0 = P := by
  rw [P.likelihoodWidePath_eq_quarter h hh hb hm (by norm_num),P.likelihoodPath_zero h hh hb hm]

lemma RandomizedPolicy.hasDerivAt_normalizedRegret_likelihoodWidePath (π : RandomizedPolicy n)
    (P : Instance n) {H lam : ℝ} (hH : 0 ≤ H) (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Icc (-(1 / 4) : ℝ) (1 / 4)) :
    HasDerivAt (fun t => π.normalizedRegret (P.likelihoodWidePath h hh hb hm t) lam)
      (deriv (fun t => optimalScalarValue (P.likelihoodWidePath h hh hb hm t) lam (1-lam)) θ -
        deriv (fun t => π.scalarObjective (P.likelihoodWidePath h hh hb hm t) lam (1-lam)) θ) θ := by
  have hHalf : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := by constructor <;> linarith [hθ.1,hθ.2]
  have hV := (P.hasDerivAt_optimalScalarValue_likelihoodWidePath hlam.1 (sub_pos.mpr hlam.2) hH hbound h hh hb hm hHalf).differentiableAt.hasDerivAt
  have hJ := (π.hasDerivAt_scalarObjective_likelihoodWidePath P hlam.1.le (sub_nonneg.mpr hlam.2.le)
    hH hbound h hh hb hm hHalf).differentiableAt.hasDerivAt
  exact hV.sub hJ

lemma RandomizedPolicy.lawRegret_deriv_lipschitz (π : RandomizedPolicy n) (P : Instance n)
    {H δ lam : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ) (hlam : lam ∈ Icc δ (1-δ))
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Icc (-(1/4) : ℝ) (1/4)) (hρ : ρ ∈ Icc (-(1/4) : ℝ) (1/4)) :
    |deriv (fun t => π.normalizedRegret (P.likelihoodWidePath h hh hb hm t) lam) ρ -
      deriv (fun t => π.normalizedRegret (P.likelihoodWidePath h hh hb hm t) lam) θ| ≤
      ((lawCurvatureConstant H δ + 8 * (H+1)) * (1+P.totalFirstMoment) * information P.law h) * |ρ-θ| := by
  have hlam' : lam ∈ Ioo (0 : ℝ) 1 := ⟨hδ.trans_le hlam.1,by linarith [hlam.2]⟩
  rw [(π.hasDerivAt_normalizedRegret_likelihoodWidePath P hH hlam' hbound h hh hb hm hρ).deriv,
    (π.hasDerivAt_normalizedRegret_likelihoodWidePath P hH hlam' hbound h hh hb hm hθ).deriv]
  have hV := P.lawScalarUnit_deriv_lipschitz_uniform hH hδ hlam hbound h hh hb hm hθ hρ
  have hJ := π.fixedLaw_deriv_lipschitz_information P hlam'.1.le (sub_nonneg.mpr hlam'.2.le)
    hH hbound h hh hb hm hθ hρ
  have htriangle : ∀ a b c d : ℝ, |(a-b)-(c-d)| ≤ |a-c|+|b-d| := by
    intro a b c d
    have he : (a-b)-(c-d)=(a-c)-(b-d) := by ring
    rw [he]
    exact abs_sub _ _
  apply (htriangle _ _ _ _).trans ((add_le_add hV hJ).trans ?_)
  have hS := P.totalFirstMoment_nonnegative
  have hI := information_nonnegative P.law h
  have hpay : lam * H + (1-lam) ≤ H+1 := by
    have hmH := mul_le_mul_of_nonneg_right hlam'.2.le hH
    nlinarith only [hmH,hlam'.1.le]
  have hExtra : 0 ≤ 8 * (H+1) * P.totalFirstMoment * information P.law h := by positivity
  have hPayBound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpay (by norm_num : (0 : ℝ) ≤ 8)) hI
  have hdist := mul_le_mul_of_nonneg_right hPayBound (abs_nonneg (ρ-θ))
  have hExtraDist := mul_nonneg hExtra (abs_nonneg (ρ-θ))
  nlinarith only [hdist,hExtraDist]

end ProphetSecretary.Model
