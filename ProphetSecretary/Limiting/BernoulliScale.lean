import ProphetSecretary.Limiting.BernoulliValueComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Explicit rare-probability scales for finite Poisson approximation

For intensity rate≥0, k_m=ceil(rate)+m+1 and p_m=rate/k_m satisfy the hard probability
constraint p_m∈[0,1] on every m. Their total intensity is exactly rate and their
square-sum k_m p_m² tends to zero before any other limit is taken.
-/

open Filter Set MeasureTheory
open scoped Topology

namespace ProphetSecretary.Limiting

noncomputable def bernoulliMultiplicity (rate : ℝ) (m : ℕ) : ℕ := Nat.ceil rate + m + 1

lemma bernoulliMultiplicity_positive (rate : ℝ) (m : ℕ) : 0 < bernoulliMultiplicity rate m := by
  unfold bernoulliMultiplicity
  omega

noncomputable def bernoulliProbability (rate : ℝ) (hrate : 0 ≤ rate) (m : ℕ) : unitInterval :=
  ⟨rate / (bernoulliMultiplicity rate m : ℝ), div_nonneg hrate (Nat.cast_nonneg _), by
    have hd : (0 : ℝ) < bernoulliMultiplicity rate m := Nat.cast_pos.mpr (bernoulliMultiplicity_positive rate m)
    apply (div_le_one hd).mpr
    have hceil := Nat.le_ceil rate
    have hmul : (Nat.ceil rate : ℝ) ≤ bernoulliMultiplicity rate m := by
      exact_mod_cast (show Nat.ceil rate ≤ bernoulliMultiplicity rate m by unfold bernoulliMultiplicity; omega)
    exact hceil.trans hmul⟩

lemma bernoulliProbability_total (rate : ℝ) (hrate : 0 ≤ rate) (m : ℕ) :
    (bernoulliMultiplicity rate m : ℝ) * (bernoulliProbability rate hrate m : ℝ) = rate := by
  have hd : (bernoulliMultiplicity rate m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (bernoulliMultiplicity_positive rate m))
  change (bernoulliMultiplicity rate m : ℝ) * (rate / (bernoulliMultiplicity rate m : ℝ)) = rate
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hd]

lemma bernoulliProbability_squareSum (rate : ℝ) (hrate : 0 ≤ rate) (m : ℕ) :
    (bernoulliMultiplicity rate m : ℝ) * (bernoulliProbability rate hrate m : ℝ) ^ 2 =
      rate ^ 2 / (bernoulliMultiplicity rate m : ℝ) := by
  have hd : (bernoulliMultiplicity rate m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (bernoulliMultiplicity_positive rate m))
  apply (eq_div_iff hd).mpr
  calc
    _ = ((bernoulliMultiplicity rate m : ℝ) * (bernoulliProbability rate hrate m : ℝ)) ^ 2 := by ring
    _ = rate ^ 2 := by rw [bernoulliProbability_total]

lemma bernoulliMultiplicity_tendsto_atTop (rate : ℝ) :
    Tendsto (fun m : ℕ => (bernoulliMultiplicity rate m : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
  intro m
  exact_mod_cast (show m ≤ bernoulliMultiplicity rate m by unfold bernoulliMultiplicity; omega)

lemma bernoulliProbability_squareSum_tendsto_zero (rate : ℝ) (hrate : 0 ≤ rate) :
    Tendsto (fun m : ℕ => (bernoulliMultiplicity rate m : ℝ) * (bernoulliProbability rate hrate m : ℝ) ^ 2)
      atTop (𝓝 0) := by
  simp_rw [bernoulliProbability_squareSum]
  exact tendsto_const_nhds.div_atTop (bernoulliMultiplicity_tendsto_atTop rate)

lemma bernoulliProbability_error_tendsto_zero (rate : ℝ) (hrate : 0 ≤ rate) (w M : ℝ) :
    Tendsto (fun m : ℕ =>
      (bernoulliMultiplicity rate m : ℝ) * (w * (bernoulliProbability rate hrate m : ℝ) ^ 2 * M) +
      (Real.pi / 2) * w * M * Real.sqrt ((bernoulliMultiplicity rate m : ℝ) * (bernoulliProbability rate hrate m : ℝ) ^ 2))
      atTop (𝓝 0) := by
  have hs := bernoulliProbability_squareSum_tendsto_zero rate hrate
  have hfirst := hs.const_mul (w * M)
  have hsecond := (Real.continuous_sqrt.tendsto 0 |>.comp hs).const_mul ((Real.pi / 2) * w * M)
  have h := hfirst.add hsecond
  simp only [mul_zero, Real.sqrt_zero, add_zero] at h
  convert h using 1
  funext m
  dsimp only [Function.comp_apply]
  ring

end ProphetSecretary.Limiting
