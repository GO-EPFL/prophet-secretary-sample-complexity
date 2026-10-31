import ProphetSecretary.Limiting.CountableIndividualDisplacement
import ProphetSecretary.Limiting.CountableAmbientCap

/-!
# A two-sided individual value perturbation

The displayed value is x+θφ(x) near zero and the original value outside a
fixed neighborhood. A certified ambient cap larger by one accommodates both
signs. The explicit radius preserves nonnegativity because φ vanishes below
a fixed positive level.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def individualValueRadius (D b : ℝ) : ℝ := min 1 (b/2)/(D+1)

lemma individualValueRadius_pos {D b : ℝ} (hD : 0≤D) (hb : 0<b) : 0< individualValueRadius D b := by
  unfold individualValueRadius
  exact div_pos (lt_min zero_lt_one (half_pos hb)) (by positivity)

noncomputable def individualValueDisplay (φ : ℝ → ℝ) (D b θ x : ℝ) : ℝ :=
  if |θ|≤ individualValueRadius D b then x+θ*φ x else x

lemma measurable_individualValueDisplay {φ : ℝ → ℝ} (hφ : Measurable φ) (D b θ : ℝ) :
    Measurable (individualValueDisplay φ D b θ) := by
  by_cases hθ : |θ|≤ individualValueRadius D b
  · change Measurable (fun x => if |θ|≤ individualValueRadius D b then x+θ*φ x else x)
    simp only [if_pos hθ]
    exact measurable_id.add (hφ.const_mul θ)
  · change Measurable (fun x => if |θ|≤ individualValueRadius D b then x+θ*φ x else x)
    simp only [if_neg hθ]
    exact measurable_id

lemma individualValueDisplay_zero (φ : ℝ → ℝ) (D b : ℝ) : individualValueDisplay φ D b 0=id := by
  funext x
  unfold individualValueDisplay
  split_ifs <;> simp only [zero_mul,add_zero,id_eq]

lemma individualValueDisplay_supported (B : CountableInstance) (i : ℕ) {φ : ℝ → ℝ} {D b : ℝ}
    (hD : 0≤D) (hb : 0<b) (hBound : ∀ x, |φ x|≤D) (hVanish : ∀ x, x<b → φ x=0) (θ : ℝ) :
    ∀ᵐ x ∂(B.individuals i : Measure ℝ), individualValueDisplay φ D b θ x∈Icc (0 : ℝ) (B.cap+1 : ℝ≥0) := by
  filter_upwards [B.individual_supported i] with x hx
  by_cases hθ : |θ|≤ individualValueRadius D b
  · rw [individualValueDisplay,if_pos hθ]
    by_cases hxb : x<b
    · rw [hVanish x hxb,mul_zero,add_zero]
      exact ⟨hx.1,hx.2.trans (by simp only [NNReal.coe_add,NNReal.coe_one]; linarith)⟩
    · have hAmp : |θ * φ x|≤min 1 (b/2) := by
        calc
          _ = |θ| * |φ x| := abs_mul _ _
          _ ≤ |θ| * D := mul_le_mul_of_nonneg_left (hBound x) (abs_nonneg _)
          _ ≤ |θ| * (D+1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
          _ ≤ min 1 (b/2) := (le_div_iff₀ (by positivity : 0<D+1)).mp hθ
      have hAmpLow := (abs_le.mp (hAmp.trans (min_le_right _ _))).1
      have hAmpHigh := (abs_le.mp (hAmp.trans (min_le_left _ _))).2
      simp only [NNReal.coe_add,NNReal.coe_one]
      exact ⟨by linarith only [not_lt.mp hxb,hAmpLow,hb],by linarith only [hx.2,hAmpHigh]⟩
  · rw [individualValueDisplay,if_neg hθ]
    exact ⟨hx.1,hx.2.trans (by simp only [NNReal.coe_add,NNReal.coe_one]; linarith)⟩

noncomputable def individualValuePath (B : CountableInstance) (i : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (D b : ℝ) (hD : 0≤D) (hb : 0<b) (hBound : ∀ x, |φ x|≤D) (hVanish : ∀ x, x<b → φ x=0) (θ : ℝ) : CountableInstance :=
  (B.withCap (B.cap+1) (by simp)).mapIndividual i (individualValueDisplay φ D b θ)
    (measurable_individualValueDisplay hφ D b θ) (B.individualValueDisplay_supported i hD hb hBound hVanish θ)

end ProphetSecretary.Limiting.CountableInstance
