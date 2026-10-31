import ProphetSecretary.Probability.MultiJackpotMoments
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Independent fair variable signs
The sign law is an actual finite product of fair Bernoulli laws. Global sign
reversal preserves that product law; distinct-coordinate pair moments are
computed using the product independence already proved for Bernoulli flags.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Probability
open ProphetSecretary.Model
variable {n : ℕ}

noncomputable def fairProbability : unitInterval := ⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩
noncomputable def fairSigns (n : ℕ) : Measure (Fin n → Bool) := jackpotCoins n fairProbability
instance fairSigns_probability (n : ℕ) : IsProbabilityMeasure (fairSigns n) := by unfold fairSigns; infer_instance

def variableSign (σ : Fin n → Bool) (i : Fin n) : ℝ := if σ i = true then 1 else -1
def reverseSigns (σ : Fin n → Bool) : Fin n → Bool := fun i ↦ !(σ i)

lemma abs_variableSign (σ : Fin n → Bool) (i : Fin n) : |variableSign σ i| = 1 := by
  unfold variableSign
  split_ifs <;> norm_num

lemma variableSign_reverse (σ : Fin n → Bool) (i : Fin n) : variableSign (reverseSigns σ) i = -variableSign σ i := by
  cases h : σ i <;> simp [variableSign, reverseSigns, h]

lemma fairProbability_symm : unitInterval.symm fairProbability = fairProbability := by
  apply Subtype.ext
  change (1 : ℝ) - 1 / 2 = 1 / 2
  ring

lemma reverseSigns_measurePreserving : MeasurePreserving (@reverseSigns n) (fairSigns n) (fairSigns n) := by
  have hBool : MeasurePreserving Bool.not (bernoulliMeasure true false fairProbability) (bernoulliMeasure true false fairProbability) := by
    refine ⟨measurable_of_finite _, ?_⟩
    rw [map_bernoulliMeasure]
    change bernoulliMeasure false true fairProbability = bernoulliMeasure true false fairProbability
    rw [bernoulliMeasure_def, bernoulliMeasure_def, fairProbability_symm, add_comm]
  exact measurePreserving_pi (fun _ : Fin n ↦ bernoulliMeasure true false fairProbability)
    (fun _ : Fin n ↦ bernoulliMeasure true false fairProbability) (fun _ ↦ hBool)

lemma fairSigns_integrable (F : (Fin n → Bool) → ℝ) : Integrable F (fairSigns n) := by
  apply Integrable.of_bound (measurable_of_finite F).aestronglyMeasurable (∑ σ : Fin n → Bool, |F σ|)
  exact Filter.Eventually.of_forall (fun σ ↦ by rw [Real.norm_eq_abs]; exact Finset.single_le_sum (fun τ _ ↦ abs_nonneg (F τ)) (Finset.mem_univ σ))

lemma integral_fairSigns_odd (F : (Fin n → Bool) → ℝ)
    (hOdd : ∀ σ, F (reverseSigns σ) = -F σ) : ∫ σ, F σ ∂fairSigns n = 0 := by
  have hm := reverseSigns_measurePreserving (n := n)
  have h := integral_map (μ := fairSigns n) hm.measurable.aemeasurable (measurable_of_finite F).aestronglyMeasurable
  rw [hm.map_eq] at h
  have he : (fun σ ↦ F (reverseSigns σ)) = (fun σ ↦ -F σ) := funext hOdd
  rw [he, integral_neg] at h
  linarith

@[simp] lemma integral_variableSign (i : Fin n) : ∫ σ, variableSign σ i ∂fairSigns n = 0 :=
  integral_fairSigns_odd _ (fun σ ↦ variableSign_reverse σ i)

lemma variableSign_eq_bit (σ : Fin n → Bool) (i : Fin n) : variableSign σ i = 2 * MultiJackpot.bit σ i - 1 := by
  unfold variableSign MultiJackpot.bit
  split_ifs <;> norm_num

lemma max_variableSigns_eq_bits (σ : Fin n → Bool) (i j : Fin n) :
    max (variableSign σ i) (variableSign σ j) =
      2 * MultiJackpot.bit σ i + 2 * MultiJackpot.bit σ j - 2 * (MultiJackpot.bit σ i * MultiJackpot.bit σ j) - 1 := by
  cases hi : σ i <;> cases hj : σ j <;> norm_num [variableSign, MultiJackpot.bit, hi, hj]

/-- Two distinct independent fair signs have expected maximum exactly one half. -/
lemma integral_max_variableSigns {i j : Fin n} (hij : i ≠ j) :
    (∫ σ, max (variableSign σ i) (variableSign σ j) ∂fairSigns n) = 1 / 2 := by
  have hi := MultiJackpot.integrable_bit (N := n) fairProbability i
  have hj := MultiJackpot.integrable_bit (N := n) fairProbability j
  have hijI := MultiJackpot.integrable_bit_product (N := n) fairProbability i j
  simp_rw [max_variableSigns_eq_bits]
  change (∫ σ, 2 * MultiJackpot.bit σ i + 2 * MultiJackpot.bit σ j -
    2 * (MultiJackpot.bit σ i * MultiJackpot.bit σ j) - 1 ∂jackpotCoins n fairProbability) = _
  rw [integral_sub (f := fun σ ↦ 2 * MultiJackpot.bit σ i + 2 * MultiJackpot.bit σ j -
      2 * (MultiJackpot.bit σ i * MultiJackpot.bit σ j)) (g := fun _ ↦ (1 : ℝ))
      ((hi.const_mul 2).add (hj.const_mul 2) |>.sub (hijI.const_mul 2)) (integrable_const 1),
    integral_sub (f := fun σ ↦ 2 * MultiJackpot.bit σ i + 2 * MultiJackpot.bit σ j)
      (g := fun σ ↦ 2 * (MultiJackpot.bit σ i * MultiJackpot.bit σ j))
      ((hi.const_mul 2).add (hj.const_mul 2)) (hijI.const_mul 2),
    integral_add (f := fun σ ↦ 2 * MultiJackpot.bit σ i) (g := fun σ ↦ 2 * MultiJackpot.bit σ j)
      (hi.const_mul 2) (hj.const_mul 2), integral_const_mul, integral_const_mul, integral_const_mul,
    MultiJackpot.integral_bit, MultiJackpot.integral_bit, MultiJackpot.integral_bit_product fairProbability hij]
  norm_num [fairProbability]


lemma integrable_integral_fairSigns {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : (Fin n → Bool) → Ω → ℝ) (hF : ∀ σ, Integrable (F σ) μ) :
    Integrable (fun ω ↦ ∫ σ, F σ ω ∂fairSigns n) μ := by
  have hEq : (fun ω ↦ ∫ σ, F σ ω ∂fairSigns n) =
      (fun ω ↦ ∑ σ : Fin n → Bool, (fairSigns n).real {σ} * F σ ω) := by
    funext ω
    simpa only [smul_eq_mul] using integral_fintype (fairSigns_integrable (fun σ ↦ F σ ω))
  rw [hEq]
  exact integrable_finsetSum _ (fun σ _ ↦ (hF σ).const_mul _)

/-- Finite sign averaging commutes with every integrable family. -/
lemma integral_fairSigns_integral_swap {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : (Fin n → Bool) → Ω → ℝ) (hF : ∀ σ, Integrable (F σ) μ) :
    (∫ σ, ∫ ω, F σ ω ∂μ ∂fairSigns n) = ∫ ω, ∫ σ, F σ ω ∂fairSigns n ∂μ := by
  calc
    _ = ∑ σ : Fin n → Bool, (fairSigns n).real {σ} * ∫ ω, F σ ω ∂μ := by
      simpa only [smul_eq_mul] using integral_fintype (fairSigns_integrable (fun σ ↦ ∫ ω, F σ ω ∂μ))
    _ = ∫ ω, ∑ σ : Fin n → Bool, (fairSigns n).real {σ} * F σ ω ∂μ := by
      rw [integral_finsetSum _ (fun σ _ ↦ (hF σ).const_mul _)]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω ↦ by
        simpa only [smul_eq_mul] using (integral_fintype (fairSigns_integrable (fun σ ↦ F σ ω))).symm)

end ProphetSecretary.Probability
