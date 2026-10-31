import ProphetSecretary.Probability.LikelihoodRebase

/-!
# A continuous scalar parameter extension of the likelihood laws

Clamping to the wider half interval leaves a neighborhood of every manuscript
parameter unchanged. Regularity is asserted only on the open half interval,
which contains the closed manuscript quarter interval.
-/

open MeasureTheory Set
open scoped Topology

namespace ProphetSecretary.Probability

noncomputable def halfParameter (θ : ℝ) : ℝ := max (-(1 / 2)) (min (1 / 2) θ)

lemma halfParameter_mem (θ : ℝ) : halfParameter θ ∈ Icc (-(1 / 2) : ℝ) (1 / 2) :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma halfParameter_abs_le (θ : ℝ) : |halfParameter θ| ≤ 1 / 2 := abs_le.mpr (halfParameter_mem θ)

lemma halfParameter_of_mem {θ : ℝ} (hθ : |θ| ≤ 1 / 2) : halfParameter θ = θ := by
  have ht := abs_le.mp hθ
  exact (max_eq_right (ht.1.trans_eq (min_eq_right ht.2).symm)).trans (min_eq_right ht.2)

lemma continuous_halfParameter : Continuous halfParameter :=
  continuous_const.max (continuous_const.min continuous_id)

end ProphetSecretary.Probability

namespace ProphetSecretary.Model.Instance

open ProphetSecretary.Probability

variable {n : ℕ}

noncomputable def likelihoodWidePath (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) (θ : ℝ) : Instance n :=
  P.likelihoodWideTilt h hh hb hm (halfParameter θ) (halfParameter_abs_le θ)

lemma likelihoodWidePath_of_mem (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 2) :
    P.likelihoodWidePath h hh hb hm θ = P.likelihoodWideTilt h hh hb hm θ hθ := by
  apply Instance.ext_law
  funext i
  change tiltLaw (P.law i) (h i) (halfParameter θ) = tiltLaw (P.law i) (h i) θ
  rw [halfParameter_of_mem hθ]

lemma likelihoodWidePath_eq_quarter (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    P.likelihoodWidePath h hh hb hm θ = P.likelihoodPath h hh hb hm θ := by
  rw [P.likelihoodWidePath_of_mem h hh hb hm (hθ.trans (by norm_num)),
    P.likelihoodPath_of_mem h hh hb hm hθ, P.likelihoodWideTilt_eq_quarter h hh hb hm θ hθ]

lemma likelihoodWidePath_bounded (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) (θ : ℝ)
    {H : ℝ} (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    ∀ i, ∀ᵐ x ∂(P.likelihoodWidePath h hh hb hm θ).law i, x ≤ H :=
  P.likelihoodWideTilt_bounded h hh hb hm _ _ hbound

end ProphetSecretary.Model.Instance
