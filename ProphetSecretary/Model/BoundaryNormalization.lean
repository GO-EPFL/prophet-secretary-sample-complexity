import ProphetSecretary.Model.Scaling
import ProphetSecretary.Reach.Robust

/-!
# Normalizing a finite reward-boundary counterexample

A positive lower bound mu on M makes division by M uniform: offers originally
bounded by H become bounded by H/mu. Reward-only value and its gap scale exactly.
-/

open MeasureTheory Set
open scoped NNReal
namespace ProphetSecretary.Model
variable {n : ℕ}

noncomputable def boundaryNormalizedCap (H : ℝ≥0) (mu : ℝ) (hmu : 0<mu) : ℝ≥0 :=
  ⟨(H:ℝ)/mu,div_nonneg H.property hmu.le⟩

noncomputable def Instance.normalizeMaximum (P : Instance n) (hM : 0<P.expectedMaximum) : Instance n :=
  P.scale (1/P.expectedMaximum) (by positivity)

lemma Instance.normalizeMaximum_expectedMaximum (P : Instance n) (hM : 0<P.expectedMaximum) :
    (P.normalizeMaximum hM).expectedMaximum=1 := by
  rw [normalizeMaximum,scale_expectedMaximum]
  field_simp

lemma Instance.normalizeMaximum_bounded (P : Instance n) {H : ℝ≥0} {mu : ℝ} (hmu : 0<mu)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤(H:ℝ)) (hMean : mu≤P.expectedMaximum) (i : Fin n) :
    ∀ᵐ x ∂(P.normalizeMaximum (hmu.trans_le hMean)).law i, x≤(boundaryNormalizedCap H mu hmu:ℝ) := by
  have hM : 0<P.expectedMaximum := hmu.trans_le hMean
  apply (ae_map_iff (measurable_valueScale (1/P.expectedMaximum)).aemeasurable measurableSet_Iic).mpr
  have hInv : 1/P.expectedMaximum≤1/mu := one_div_le_one_div_of_le hmu hMean
  filter_upwards [P.nonnegative i,hcap i] with x hx0 hxH
  change (1/P.expectedMaximum)*x≤(H:ℝ)/mu
  have h := mul_le_mul hInv hxH hx0 (by positivity : 0≤1/mu)
  calc
    _ ≤ (1/mu)*(H:ℝ) := h
    _ = _ := by ring

lemma Instance.normalizeMaximum_rewardValue (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (hM : 0<P.expectedMaximum) :
    optimalScalarValue (P.normalizeMaximum hM) 1 0=optimalScalarValue P 1 0/P.expectedMaximum := by
  have hA : 0<1/P.expectedMaximum := by positivity
  rw [normalizeMaximum,optimalScalarValue_scale P (1/P.expectedMaximum) hA hP zero_le_one le_rfl]
  have h := optimalScalarValue_smul P hP hA.le zero_le_one le_rfl
  change optimalScalarValue P ((1/P.expectedMaximum)*1) ((1/P.expectedMaximum)*0)=
    (1/P.expectedMaximum)*optimalScalarValue P 1 0 at h
  rw [mul_zero] at h
  rw [h]
  ring

lemma Instance.normalizeMaximum_rewardGap (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (hM : 0<P.expectedMaximum) :
    optimalScalarValue (P.normalizeMaximum hM) 1 0-optimalCompetitiveRatio=
      (optimalScalarValue P 1 0-optimalCompetitiveRatio*P.expectedMaximum)/P.expectedMaximum := by
  rw [P.normalizeMaximum_rewardValue hP hM]
  field_simp [ne_of_gt hM]

end ProphetSecretary.Model
