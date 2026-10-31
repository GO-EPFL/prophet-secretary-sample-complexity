import ProphetSecretary.Limiting.PoissonizedFamily
import ProphetSecretary.Limiting.IndependentAppend
import ProphetSecretary.Limiting.ZeroIntensity

/-!
# Degenerate zero positive intensity

A nonnegative marginal with no positive mass is the point mass at zero. Thus
zero total positive intensity means every replaced variable is identically
zero. The finite and Poissonized values then agree by the two proved zero
simulation identities, including zero-maximum auxiliary instances.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Limiting

variable {n m : ℕ}

lemma positiveOfferIntensity_zero_laws (R : Model.Instance m) (hμ : positiveOfferIntensity R = 0) :
    ∀ i, R.law i = Measure.dirac 0 := by
  have hsum : (∑ i, (R.law i).real (Ioi 0)) = 0 := by
    change R.positiveCount = 0
    rw [← positiveOfferIntensity_mass R,hμ]
    rfl
  intro i
  have hz : (R.law i).real (Ioi 0) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => measureReal_nonneg)).mp hsum i (Finset.mem_univ i)
  have hnull : R.law i (Ioi 0) = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz
  have hno : ∀ᵐ x ∂R.law i, ¬0 < x := (measure_eq_zero_iff_ae_notMem).mp hnull
  have heq : (id : ℝ → ℝ) =ᵐ[R.law i] (fun _ => 0) := by
    filter_upwards [R.nonnegative i,hno] with x hx hn
    exact le_antisymm (not_lt.mp hn) hx
  calc
    _ = (R.law i).map id := (Measure.map_id).symm
    _ = (R.law i).map (fun _ => 0) := Measure.map_congr heq
    _ = _ := by rw [Measure.map_const, measure_univ, one_smul]

lemma independentAppend_eq_appendZeros_of_zeroIntensity (P : Model.Instance n) (R : Model.Instance m)
    (hμ : positiveOfferIntensity R = 0) : P.appendIndependent R = P.appendZeros m := by
  apply Model.Instance.eq_of_law_eq
  funext i
  induction i using Fin.addCases with
  | left i => simp only [Model.Instance.appendIndependent, Model.Instance.appendZeros, Fin.addCases_left]
  | right j =>
    simp only [Model.Instance.appendIndependent, Model.Instance.appendZeros, Fin.addCases_right]
    exact positiveOfferIntensity_zero_laws R hμ j

lemma causalPoisson_zeroTerminal_zeroIntensity (P : Model.Instance n) (R : Model.Instance m)
    (H : ℝ≥0) (hPcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hRcap : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) (hμ : positiveOfferIntensity R = 0)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Model.optimalScalarValue (P.appendIndependent R) w c =
      (poissonizedFamily P R H hPcap hRcap).optimalScalarValue w c := by
  rw [independentAppend_eq_appendZeros_of_zeroIntensity P R hμ,
    P.optimalScalarValue_appendZeros m (P.integrable_maximum_of_bounded hPcap) hw hc,
    (poissonizedFamily P R H hPcap hRcap).value_zero_intensity (by rfl) hμ hw hc]
  rfl

end ProphetSecretary.Limiting
