import ProphetSecretary.Model.LawBranchIntegration
import ProphetSecretary.Model.LawBranchLimit
import ProphetSecretary.Stability.WideLikelihoodEnergy
import ProphetSecretary.Probability.RestrictedInformation

/-!
# The finite directional adaptation kernel

The law derivative holds the old continuation coefficient fixed. The time
slope is the derivative with respect to that coefficient. The kernel is zero
outside positive interior roots; the actual pending/state multiplier retains
all revealed identities and supplies the reach factor.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

noncomputable def Instance.lawStateParameterDerivative (P : Instance n)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (w θ : ℝ) (A : Finset (Fin n)) (d : ℝ) : ℝ :=
  deriv (fun q ↦ optimalScalarValue ((P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) q) w d) θ

noncomputable def Instance.lawStateCoefficientDerivative (P : Instance n)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (w θ : ℝ) (A : Finset (Fin n)) (d : ℝ) : ℝ :=
  deriv (remainingScalarValue ((P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) θ) w 1) d

lemma Instance.lawStateCoefficientDerivative_positive (P : Instance n) {w H d : ℝ}
    (hw : 0 < w) (hd : 0 < d) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ : ℝ) (A : Finset (Fin n)) : 0 < P.lawStateCoefficientDerivative h hh hb hm w θ A d := by
  let Q := (P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) θ
  have hQB := (P.restrictTo A).likelihoodWidePath_bounded (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) θ
    (fun j ↦ hbound (stateEmbedding A j))
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (4 * (1 + (A.card : ℝ))))
    (remainingScalarValue_deriv_ge_card_bound Q (Q.integrable_maximum_of_bounded hQB) hw zero_le_one hd)

noncomputable def Instance.lawAdaptationKernel (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ : ℝ) (i : Fin n) (A : Finset (Fin n)) (ω : World n Unit) : ℝ :=
  let Q := P.likelihoodWidePath h hh hb hm θ
  let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let d := P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i)
  if 0 < d ∧ d < c then
    (Q.valuePolicy hQ hw.le hc).rule.branchMultiplier () ω.1 ω.2.1 i A (1 - d / c) *
      P.lawStateParameterDerivative h hh hb hm w θ A d ^ 2 /
        (c * P.lawStateCoefficientDerivative h hh hb hm w θ A d) else 0

lemma Instance.lawAdaptationKernel_nonnegative (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ : ℝ) (i : Fin n) (A : Finset (Fin n)) (ω : World n Unit) :
    0 ≤ P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω := by
  unfold Instance.lawAdaptationKernel
  dsimp only
  split_ifs with hd
  · exact div_nonneg (mul_nonneg (Policy.branchMultiplier_mem_unit _ _ _ _ _ _ _).1 (sq_nonneg _))
      (mul_pos hc (P.lawStateCoefficientDerivative_positive hw hd.1 hbound h hh hb hm θ A)).le
  · exact le_rfl

end ProphetSecretary.Model
