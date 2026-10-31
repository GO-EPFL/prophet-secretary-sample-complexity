import ProphetSecretary.Statistics.NormalizedGameKernel
import ProphetSecretary.Model.SmoothEnvelopeDuration
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Actual law response of a fixed base-optimal kernel

The fixed policy's kernel is differentiated first. Reoptimized-value response
is identified separately: the actual nonnegative regret of a base optimizer
has derivative zero. No policy is reselected inside the kernel derivative.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem RandomizedPolicy.hasDerivAt_normalizedGameKernel_mean (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {lam : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    HasDerivAt (fun t => π.scalarObjective (P.likelihoodWidePath h hh hb hm t) lam (1-lam) -
      optimalCompetitiveRatio*(lam*(P.likelihoodWidePath h hh hb hm t).expectedMaximum+(1-lam)))
      (∫ x, π.normalizedGameKernel lam x*completeScore h x ∂P.valuesLaw) 0 := by
  have hlam' : lam ∈ Ioc (0 : ℝ) 1 := ⟨hlam.1,hlam.2.le⟩
  have hd := hasDerivAt_fixedPayoff_law_zero P.law h hh hb hm (π.normalizedGameKernel lam)
    (π.measurable_normalizedGameKernel lam) zero_le_one (π.normalizedGameKernel_abs_le_ae P hcap hlam')
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (by norm_num : (-(1/4) : ℝ) < 0) (by norm_num : (0 : ℝ) < 1/4)] with t ht
  have ht' : |t| ≤ 1/4 := abs_le.mpr ht
  rw [← π.integral_normalizedGameKernel (P.likelihoodWidePath h hh hb hm t)
    (P.likelihoodWidePath_bounded h hh hb hm t hcap) hlam',
    P.likelihoodWidePath_eq_quarter h hh hb hm ht',P.likelihoodPath_of_mem h hh hb hm ht']
  rfl

lemma RandomizedPolicy.deriv_normalizedRegret_zero_of_opt (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {lam : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (hOpt : π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam))
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    deriv (fun t => π.normalizedRegret (P.likelihoodWidePath h hh hb hm t) lam) 0 = 0 := by
  let R := fun t => π.normalizedRegret (P.likelihoodWidePath h hh hb hm t) lam
  have hR0 : R 0 = 0 := by
    dsimp only [R]
    rw [P.likelihoodWidePath_zero_eq h hh hb hm]
    exact sub_eq_zero.mpr hOpt.symm
  have hMin : IsLocalMin R 0 := by
    apply Filter.Eventually.of_forall
    intro t
    rw [hR0]
    exact π.normalizedRegret_nonnegative _
      ((P.likelihoodWidePath h hh hb hm t).integrable_maximum_of_bounded
        (P.likelihoodWidePath_bounded h hh hb hm t hcap)) ⟨hlam.1.le,hlam.2.le⟩
  have hDeriv := π.hasDerivAt_normalizedRegret_likelihoodWidePath P zero_le_one hlam hcap h hh hb hm
    (show (0 : ℝ) ∈ Icc (-(1/4) : ℝ) (1/4) by norm_num)
  exact hDeriv.deriv.trans (hMin.hasDerivAt_eq_zero hDeriv)

theorem RandomizedPolicy.deriv_normalizedGap_eq_kernelScore_of_opt (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {lam : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (hOpt : π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam))
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    deriv (fun t => normalizedScalarGap (P.likelihoodWidePath h hh hb hm t) lam) 0 =
      ∫ x, π.normalizedGameKernel lam x*completeScore h x ∂P.valuesLaw := by
  have hIdentity := π.normalizedScoreResponse_eq_gap_sub_regret_deriv P zero_le_one hlam hcap h hh hb hm
  rw [π.deriv_normalizedRegret_zero_of_opt P hcap hlam hOpt h hh hb hm,sub_zero] at hIdentity
  have hKernel := π.hasDerivAt_normalizedGameKernel_mean P hcap hlam h hh hb hm
  have hScore : HasDerivAt (fun t => π.scalarObjective (P.likelihoodWidePath h hh hb hm t) lam (1-lam) -
      optimalCompetitiveRatio*(lam*(P.likelihoodWidePath h hh hb hm t).expectedMaximum+(1-lam)))
      (π.normalizedScoreResponse P h lam) 0 := by
    have heq : (fun t => π.scalarObjective (P.likelihoodWidePath h hh hb hm t) lam (1-lam) -
        optimalCompetitiveRatio*(lam*(P.likelihoodWidePath h hh hb hm t).expectedMaximum+(1-lam))) =
        (fun t => π.scalarObjective (P.likelihoodWidePath h hh hb hm t) lam (1-lam) -
        optimalCompetitiveRatio*(lam*(P.likelihoodWidePath h hh hb hm t).expectedMaximum+1-lam)) := by
      funext t
      ring
    rw [heq]
    exact π.hasDerivAt_normalizedScoreResponse P zero_le_one hcap ⟨hlam.1.le,hlam.2.le⟩ h hh hb hm
  exact hIdentity.symm.trans (hScore.deriv.symm.trans hKernel.deriv)

lemma Instance.hasDerivAt_normalizedGap_wide (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {lam : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Icc (-(1/4) : ℝ) (1/4)) :
    HasDerivAt (fun t => normalizedScalarGap (P.likelihoodWidePath h hh hb hm t) lam)
      (deriv (fun t => normalizedScalarGap (P.likelihoodWidePath h hh hb hm t) lam) θ) θ := by
  have hHalf : θ ∈ Ioo (-(1/2) : ℝ) (1/2) := by constructor <;> linarith [hθ.1,hθ.2]
  have hV := (P.hasDerivAt_optimalScalarValue_likelihoodWidePath hlam.1 (sub_pos.mpr hlam.2)
    zero_le_one hcap h hh hb hm hHalf).differentiableAt
  have hM := (P.expectedMaximum_likelihoodWidePath_twice_differentiable zero_le_one hcap h hh hb hm hHalf).1
  exact (hV.sub (((hM.const_mul lam).add_const (1-lam)).const_mul optimalCompetitiveRatio)).hasDerivAt

end ProphetSecretary.Model
