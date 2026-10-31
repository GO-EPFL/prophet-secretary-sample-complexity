import ProphetSecretary.Limiting.FinitePotentialResidual

/-!
# Joint measurability of the finite continuation potential

This is a finite design's value indexed by the current unseen individual set.
Its evaluation at measurable time and clock maps is measurable. It does not
assume existence of a canonical optimizer for the limiting hybrid problem.
-/

open MeasureTheory Set

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_poissonContinuationBy (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (T : Ω → ℝ) (U : Ω → Fin n → ℝ) (hT : Measurable T)
    (hU : ∀ i, Measurable (fun q => U q i)) :
    Measurable (fun q => poissonContinuation Q w c (U q) (T q)) := by
  have hH : Measurable (fun q => Model.unseen (Model.history Finset.univ (fun _ => 0) (U q) (T q))) :=
    Model.measurable_unseen.comp (Model.measurable_history Finset.univ (fun _ => measurable_const) hU hT)
  have hθ := (measurable_poissonThreshold Q hQ hw.le hc).comp (hH.prodMk hT)
  have heq : (fun q => poissonContinuation Q w c (U q) (T q)) =
      (fun q => w * poissonThreshold Q w c (Model.unseen (Model.history Finset.univ (fun _ => 0) (U q) (T q))) (T q)) := by
    funext q
    unfold poissonContinuation poissonThreshold
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hw.ne']
  rw [heq]
  exact hθ.const_mul w

end ProphetSecretary.Limiting
