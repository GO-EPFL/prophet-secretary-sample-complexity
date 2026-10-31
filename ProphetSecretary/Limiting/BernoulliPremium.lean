import ProphetSecretary.Limiting.BernoulliPotential

/-!
# Current-state and deleted-state Bernoulli premiums

Deleting one virtual Bernoulli offer changes continuation by at most its first
moment. The positive-part reward is one-Lipschitz in this continuation value,
so the rate-weighted discrepancy is quadratic in the rare probability.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

lemma positivePremium_difference_le (κ : Measure ℝ) [IsProbabilityMeasure κ] (hI : Integrable id κ)
    (w : ℝ) {v v' : ℝ} (hvv : v ≤ v') :
    0 ≤ Model.positivePremium κ w v - Model.positivePremium κ w v' ∧
      Model.positivePremium κ w v - Model.positivePremium κ w v' ≤ v' - v := by
  have hi := Model.integrable_positivePart κ hI w v
  have hi' := Model.integrable_positivePart κ hI w v'
  have hm : Model.positivePremium κ w v' ≤ Model.positivePremium κ w v := by
    apply integral_mono hi' hi
    intro x
    exact max_le_max (sub_le_sub_left hvv _) le_rfl
  have hb : Model.positivePremium κ w v ≤ Model.positivePremium κ w v' + (v' - v) := by
    have h := integral_mono hi (hi'.add (integrable_const (v' - v))) (fun x => by
      change max (w * x - v) 0 ≤ max (w * x - v') 0 + (v' - v)
      apply max_le
      · linarith only [le_max_left (w * x - v') (0 : ℝ)]
      · exact add_nonneg (le_max_right _ _) (sub_nonneg.mpr hvv))
    change (∫ x, max (w * x - v) 0 ∂κ) ≤ ∫ x, max (w * x - v') 0 + (v' - v) ∂κ at h
    rw [integral_add hi' (integrable_const _)] at h
    simpa only [Model.positivePremium, integral_const, probReal_univ, smul_eq_mul, one_mul] using h
  exact ⟨sub_nonneg.mpr hm, by linarith only [hb]⟩

variable {n : ℕ}

lemma finitePoissonDesign_child_premium_gap (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval) (k : ℕ)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hI : Integrable id κ)
    (A : Finset (Fin (n + k))) (j : Fin k) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let Q := finitePoissonDesign P κ hκ p k
    let v := Model.optimalScalarValue (Q.restrictTo A) w c
    let vChild := Model.optimalScalarValue (Q.restrictTo (A.erase (j.natAdd n))) w c
    0 ≤ Model.positivePremium κ w vChild - Model.positivePremium κ w v ∧
      Model.positivePremium κ w vChild - Model.positivePremium κ w v ≤ w * (p : ℝ) * ∫ x, x ∂κ := by
  have hd := finitePoissonDesign_virtual_deletion P κ hκ p k hP hI A j hw hc
  have hp := positivePremium_difference_le κ hI w (sub_nonneg.mp hd.1)
  exact ⟨hp.1, hp.2.trans hd.2⟩

lemma finitePoissonDesign_weighted_child_premium_gap (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval) (k : ℕ)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hI : Integrable id κ)
    (A : Finset (Fin (n + k))) (j : Fin k) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let Q := finitePoissonDesign P κ hκ p k
    let v := Model.optimalScalarValue (Q.restrictTo A) w c
    let vChild := Model.optimalScalarValue (Q.restrictTo (A.erase (j.natAdd n))) w c
    0 ≤ (p : ℝ) * (Model.positivePremium κ w vChild - Model.positivePremium κ w v) ∧
      (p : ℝ) * (Model.positivePremium κ w vChild - Model.positivePremium κ w v) ≤
        w * (p : ℝ) ^ 2 * ∫ x, x ∂κ := by
  have h := finitePoissonDesign_child_premium_gap P κ hκ p k hP hI A j hw hc
  refine ⟨mul_nonneg p.property.1 h.1, ?_⟩
  have hu := mul_le_mul_of_nonneg_left h.2 p.property.1
  nlinarith only [hu]

end ProphetSecretary.Limiting
