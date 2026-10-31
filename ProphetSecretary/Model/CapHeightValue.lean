import ProphetSecretary.Model.ValueTransportLipschitz

/-!
# Optimized value is Lipschitz in the cap height

A second smaller cap is a deterministic value map of the larger capped
instance, with displacement at most the cap difference. The established
uniform value-transport theorem gives the reward-weight times displacement
bound, independently of the number of offers.
-/

open MeasureTheory Set Filter
open scoped NNReal Classical
namespace ProphetSecretary.Model
variable {n : ℕ}

lemma Instance.cap_cap_of_le (P : Instance n) (H K : ℝ≥0) (hKH : K≤H) : (P.cap H).cap K=P.cap K := by
  apply Instance.eq_of_law_eq
  funext i
  change ((P.law i).map (capValue H)).map (capValue K)=(P.law i).map (capValue K)
  rw [Measure.map_map (measurable_capValue K) (measurable_capValue H)]
  have hKHR : (K:ℝ)≤(H:ℝ) := by exact_mod_cast hKH
  have hFun : capValue K ∘ capValue H=capValue K := by
    funext x
    change min (min x (H:ℝ)) (K:ℝ)=min x (K:ℝ)
    rw [min_assoc,min_eq_right hKHR]
  rw [hFun]

lemma Instance.capHeight_value_error_of_le (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (K H : ℝ≥0) (hKH : K≤H) {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    |optimalScalarValue (P.cap K) w c-optimalScalarValue (P.cap H) w c|≤w*((H:ℝ)-(K:ℝ)) := by
  let Q := P.cap H
  let f : Fin n → ℝ → ℝ := fun _ => capValue K
  have hf : ∀ i, Measurable (f i) := fun _ => measurable_capValue K
  have hNn : ∀ i, ∀ᵐ x ∂Q.law i, 0≤f i x := fun i => (Q.nonnegative i).mono fun _ hx => le_min hx K.property
  have hδ : (0:ℝ)≤(H:ℝ)-(K:ℝ) := sub_nonneg.mpr hKH
  have hDisp : ∀ i, ∀ᵐ x ∂Q.law i, |f i x-x|≤(H:ℝ)-(K:ℝ) := by
    intro i
    filter_upwards [P.cap_bounded H i] with x hxH
    change |min x (K:ℝ)-x|≤(H:ℝ)-(K:ℝ)
    rw [abs_of_nonpos (sub_nonpos.mpr (min_le_left _ _))]
    by_cases hxK : x≤(K:ℝ)
    · rw [min_eq_left hxK]
      linarith only [hδ]
    · rw [min_eq_right (le_of_not_ge hxK)]
      linarith only [hxH]
  have hMap : Q.mapValues f hf hNn=P.cap K := by
    exact P.cap_cap_of_le H K hKH
  have h := Q.optimalScalarValue_mapValues_lipschitz (P.cap_integrable_maximum H hP) f hf hNn hδ hw hc hDisp
  rwa [hMap] at h

theorem Instance.capHeight_value_abs_sub_le (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (K H : ℝ≥0) {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    |optimalScalarValue (P.cap K) w c-optimalScalarValue (P.cap H) w c|≤w*|(K:ℝ)-(H:ℝ)| := by
  rcases le_total K H with hKH | hHK
  · have h := P.capHeight_value_error_of_le hP K H hKH hw hc
    have hKHR : (K:ℝ)≤(H:ℝ) := by exact_mod_cast hKH
    rw [abs_of_nonpos (sub_nonpos.mpr hKHR)]
    simpa only [neg_sub] using h
  · have h := P.capHeight_value_error_of_le hP H K hHK hw hc
    have hHKR : (H:ℝ)≤(K:ℝ) := by exact_mod_cast hHK
    rw [abs_sub_comm] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hHKR)]
    exact h

end ProphetSecretary.Model
