import ProphetSecretary.Stability.LikelihoodEnvelope
import ProphetSecretary.Probability.MarginalReplacement

/-!
# One-marginal likelihood experiments

Only one centered score is active. All other marginal laws remain exactly equal
to their base laws; independent marginal replacement therefore applies without
any conditional-law assumption.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Probability

variable {n : ℕ}

def singleScore (i : Fin n) (h : ℝ → ℝ) (j : Fin n) (x : ℝ) : ℝ := if j = i then h x else 0

lemma singleScore_measurable (i : Fin n) {h : ℝ → ℝ} (hh : Measurable h) (j : Fin n) :
    Measurable (singleScore i h j) := by
  change Measurable (fun x : ℝ ↦ if j = i then h x else 0)
  by_cases hj : j = i
  · simpa only [if_pos hj] using hh
  · simpa only [if_neg hj] using (measurable_const : Measurable (fun _ : ℝ ↦ (0 : ℝ)))

lemma singleScore_bound (μ : Fin n → Measure ℝ) (i : Fin n) {h : ℝ → ℝ}
    (hb : ∀ᵐ x ∂μ i, |h x| ≤ 1) (j : Fin n) : ∀ᵐ x ∂μ j, |singleScore i h j x| ≤ 1 := by
  by_cases hj : j = i
  · subst j
    simpa only [singleScore, if_true] using hb
  · exact Filter.Eventually.of_forall (fun x ↦ by simp [singleScore, hj])

lemma singleScore_centered (μ : Fin n → Measure ℝ) (i : Fin n) {h : ℝ → ℝ}
    (hm : ∫ x, h x ∂μ i = 0) (j : Fin n) : ∫ x, singleScore i h j x ∂μ j = 0 := by
  by_cases hj : j = i
  · subst j
    simpa only [singleScore, if_true] using hm
  · simp only [singleScore, hj, if_false, integral_zero]

lemma singleScore_complete (i : Fin n) (h : ℝ → ℝ) (x : Fin n → ℝ) : completeScore (singleScore i h) x = h (x i) := by
  unfold completeScore singleScore
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp only [hj, if_false]
  · simp

end ProphetSecretary.Probability

namespace ProphetSecretary.Model.Instance

open ProphetSecretary.Probability

variable {n : ℕ}

noncomputable def singleMarginalTilt (P : Instance n) (i : Fin n) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂P.law i, |h x| ≤ 1) (hm : ∫ x, h x ∂P.law i = 0)
    (θ : ℝ) (hθ : |θ| ≤ 1 / 4) : Instance n :=
  P.likelihoodTilt (singleScore i h) (singleScore_measurable i hh) (singleScore_bound P.law i hb)
    (singleScore_centered P.law i hm) θ hθ

lemma singleMarginalTilt_law_same (P : Instance n) (i : Fin n) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂P.law i, |h x| ≤ 1) (hm : ∫ x, h x ∂P.law i = 0)
    (θ : ℝ) (hθ : |θ| ≤ 1 / 4) : (P.singleMarginalTilt i h hh hb hm θ hθ).law i = tiltLaw (P.law i) h θ := by
  have he : singleScore i h i = h := by
    funext x
    simp only [singleScore, if_true]
  change tiltLaw (P.law i) (singleScore i h i) θ = tiltLaw (P.law i) h θ
  rw [he]

lemma singleMarginalTilt_law_other (P : Instance n) (i : Fin n) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂P.law i, |h x| ≤ 1) (hm : ∫ x, h x ∂P.law i = 0)
    (θ : ℝ) (hθ : |θ| ≤ 1 / 4) {j : Fin n} (hji : j ≠ i) :
    (P.singleMarginalTilt i h hh hb hm θ hθ).law j = P.law j := by
  simp only [singleMarginalTilt, likelihoodTilt, singleScore, hji, if_false, tiltLaw,
    tiltFactor, mul_zero, add_zero, ENNReal.ofReal_one]
  change (P.law j).withDensity 1 = P.law j
  exact withDensity_one

lemma singleMarginalTilt_bounded (P : Instance n) (i : Fin n) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂P.law i, |h x| ≤ 1) (hm : ∫ x, h x ∂P.law i = 0)
    (θ : ℝ) (hθ : |θ| ≤ 1 / 4) {H : ℝ} (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H) :
    ∀ j, ∀ᵐ x ∂(P.singleMarginalTilt i h hh hb hm θ hθ).law j, x ≤ H :=
  P.likelihoodTilt_bounded _ _ _ _ θ hθ hbound

end ProphetSecretary.Model.Instance
