import ProphetSecretary.Limiting.ZeroDesignContinuation
import ProphetSecretary.Limiting.BernoulliDriftGap

/-!
# Zero and Bernoulli laws in the retained generator

These identities specialize the proved individual-clock generator to virtual
zero observations and zero-inflated positive marks. They are pathwise algebraic
identities and do not supply future information to either policy callback.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*}

lemma HybridRule.individualPotentialDrift_zeroLaw (π : HybridRule n Seed)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (i : Fin n) (q : HybridWorld n Seed × ℝ) :
    π.individualPotentialDrift Q (Measure.dirac 0) w c i q = 0 := by
  have hv := Q.continuationAtArrival_nonnegative hQ hw hc (fun _ => 0)
    (Function.update q.1.2.2.1 i q.2) i
  unfold HybridRule.individualPotentialDrift individualDesignPremium
  split_ifs
  · simp only [Model.positivePremium, integral_dirac, mul_zero, zero_sub,
      max_eq_right (neg_nonpos.mpr hv), zero_div]
  · rfl

lemma HybridRule.individualPotentialDrift_zeroInflatedLaw (π : HybridRule n Seed)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hI : Integrable id κ) (p : unitInterval)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (i : Fin n) (q : HybridWorld n Seed × ℝ) :
    π.individualPotentialDrift Q (zeroInflatedLaw κ p) w c i q =
      (p : ℝ) * π.individualPotentialDrift Q κ w c i q := by
  have hv := Q.continuationAtArrival_nonnegative hQ hw hc (fun _ => 0)
    (Function.update q.1.2.2.1 i q.2) i
  unfold HybridRule.individualPotentialDrift individualDesignPremium
  split_ifs
  · rw [positivePremium_zeroInflatedLaw κ p hI w hv]
    ring
  · rw [mul_zero]

end ProphetSecretary.Limiting
