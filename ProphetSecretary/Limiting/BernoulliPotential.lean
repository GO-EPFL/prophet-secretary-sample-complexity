import ProphetSecretary.Limiting.FiniteArrayEvaluation
import ProphetSecretary.Model.RareVariableDeletion
import ProphetSecretary.Model.JackpotMoments
import ProphetSecretary.Model.BellmanResidualBasic

/-!
# Finite Bernoulli potentials for a Poisson intensity

A virtual offer is zero with probability `1-p` and otherwise has the given mark
law. Its continuation-state deletion cost is its actual first-moment budget,
with no factor depending on the number of retained or virtual variables.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

noncomputable def zeroInflatedLaw (κ : Measure ℝ) (p : unitInterval) : Measure ℝ :=
  Model.jackpotLaw κ (unitInterval.symm p) 0

instance zeroInflatedLaw_probability (κ : Measure ℝ) [IsProbabilityMeasure κ] (p : unitInterval) :
    IsProbabilityMeasure (zeroInflatedLaw κ p) := by unfold zeroInflatedLaw; infer_instance

lemma zeroInflatedLaw_nonnegative (κ : Measure ℝ) (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval) :
    ∀ᵐ x ∂zeroInflatedLaw κ p, 0 ≤ x := Model.jackpotLaw_nonnegative κ hκ _ le_rfl

lemma zeroInflatedLaw_integrable (κ : Measure ℝ) (p : unitInterval) {f : ℝ → ℝ} (hf : Integrable f κ) :
    Integrable f (zeroInflatedLaw κ p) := Model.jackpotLaw_integrable hf _ _

lemma integral_zeroInflatedLaw (κ : Measure ℝ) (p : unitInterval) {f : ℝ → ℝ} (hf : Integrable f κ) :
    (∫ x, f x ∂zeroInflatedLaw κ p) = (1 - (p : ℝ)) * f 0 + (p : ℝ) * ∫ x, f x ∂κ := by
  rw [zeroInflatedLaw, Model.integral_jackpotLaw hf, unitInterval.coe_symm_eq]
  ring

lemma positivePremium_zeroInflatedLaw (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (p : unitInterval) (hκ : Integrable id κ) (w : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    Model.positivePremium (zeroInflatedLaw κ p) w v = (p : ℝ) * Model.positivePremium κ w v := by
  unfold Model.positivePremium
  rw [integral_zeroInflatedLaw κ p (Model.integrable_positivePart κ hκ w v)]
  simp [max_eq_right (neg_nonpos.mpr hv)]

variable {n : ℕ}

noncomputable def finitePoissonDesign (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval) (k : ℕ) : Model.Instance (n + k) :=
  appendIID P (zeroInflatedLaw κ p) (zeroInflatedLaw_nonnegative κ hκ p) k

lemma finitePoissonDesign_integrable_maximum (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval) (k : ℕ)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hI : Integrable id κ) :
    Integrable Model.Instance.maximum (finitePoissonDesign P κ hκ p k).valuesLaw := by
  apply Model.Instance.integrable_maximum
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [finitePoissonDesign, appendIID, Fin.addCases_left] using P.integrable_maximum_iff.mp hP i
  | right j =>
    simp only [finitePoissonDesign, appendIID, Fin.addCases_right]
    exact zeroInflatedLaw_integrable κ p hI

lemma finitePoissonDesign_virtual_deletion (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval) (k : ℕ)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hI : Integrable id κ)
    (A : Finset (Fin (n + k))) (j : Fin k) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let Q := finitePoissonDesign P κ hκ p k
    0 ≤ Model.optimalScalarValue (Q.restrictTo A) w c - Model.optimalScalarValue (Q.restrictTo (A.erase (j.natAdd n))) w c ∧
      Model.optimalScalarValue (Q.restrictTo A) w c - Model.optimalScalarValue (Q.restrictTo (A.erase (j.natAdd n))) w c ≤
        w * (p : ℝ) * ∫ x, x ∂κ := by
  let Q := finitePoissonDesign P κ hκ p k
  have hQ := finitePoissonDesign_integrable_maximum P κ hκ p k hP hI
  have h := Q.optimalScalarValue_restrictTo_remove_loss A (j.natAdd n) hQ hw hc
  have hmean : (∫ x, x ∂Q.law (j.natAdd n)) = (p : ℝ) * ∫ x, x ∂κ := by
    simp only [Q, finitePoissonDesign, appendIID, Fin.addCases_right]
    simpa only [id_eq, mul_zero, zero_add] using integral_zeroInflatedLaw κ p hI
  rw [hmean] at h
  simpa only [mul_assoc] using h

end ProphetSecretary.Limiting
