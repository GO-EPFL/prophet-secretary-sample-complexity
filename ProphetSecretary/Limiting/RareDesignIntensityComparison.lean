import ProphetSecretary.Limiting.RareStopLossIncrement
import ProphetSecretary.Limiting.WeakRareDesign

/-!
# General-policy value comparison for common-size finite rare designs

Each virtual row has stop-loss error at most its share of the added first
moment. The proved finite Bellman stability theorem sums these errors exactly,
so the final constant is independent of both retained and virtual dimensions.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model
variable {n : ℕ}

theorem rareDesign_value_add_bounds (P : Model.Instance n) (μ ρ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hP : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (hρ : ∀ᵐ x ∂(ρ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (k : ℕ) (hk : 0 < k) (hm : (μ+ρ).mass ≤ (k : ℝ≥0))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    let hs : ∀ᵐ x ∂((μ+ρ : FiniteMeasure ℝ) : Measure ℝ), x ∈ Icc (0 : ℝ) H := ae_add_measure_iff.mpr ⟨hμ,hρ⟩
    let Q := rareDesign P μ H hμ k hk ((finiteMeasure_mass_le_add μ ρ).trans hm)
    let R := rareDesign P (μ+ρ) H hs k hk hm
    0 ≤ optimalScalarValue R w c-optimalScalarValue Q w c ∧
      optimalScalarValue R w c-optimalScalarValue Q w c ≤ w*(∫ x, x ∂(ρ : Measure ℝ)) := by
  dsimp only
  let hs : ∀ᵐ x ∂((μ+ρ : FiniteMeasure ℝ) : Measure ℝ), x ∈ Icc (0 : ℝ) H := ae_add_measure_iff.mpr ⟨hμ,hρ⟩
  let hmμ := (finiteMeasure_mass_le_add μ ρ).trans hm
  let Q := rareDesign P μ H hμ k hk hmμ
  let R := rareDesign P (μ+ρ) H hs k hk hm
  have hQ := Q.integrable_maximum_of_bounded (rareDesign_bounded P μ H hP hμ k hk hmμ)
  have hR := R.integrable_maximum_of_bounded (rareDesign_bounded P (μ+ρ) H hP hs k hk hm)
  have hE : 0 ≤ ∫ x, x ∂(ρ : Measure ℝ) := integral_nonneg_of_ae (hρ.mono fun _ hx => hx.1)
  have horder : Q.StopLossLE R := by
    intro i b
    induction i using Fin.addCases with
    | left i => simp only [Q,R,rareDesign,appendIID,Fin.addCases_left,le_refl]
    | right j =>
      have hb := (rareProbabilityLaw_stopLoss_add_bounds μ ρ H hμ hρ k (by exact_mod_cast hk) hm b).1
      simp only [Q,R,rareDesign,appendIID,Fin.addCases_right]
      exact sub_nonneg.mp hb
  have hlower := Q.optimalScalarValue_mono_stopLoss_nonnegative R hQ hR horder hw hc
  refine ⟨sub_nonneg.mpr hlower,?_⟩
  by_cases hw0 : w = 0
  · subst w
    rw [optimalScalarValue_zero_rewardWeight R hc,optimalScalarValue_zero_rewardWeight Q hc]
    simp
  have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  let budget : Fin (n+k) → ℝ := Fin.addCases (fun _ => 0) (fun _ => (k : ℝ)⁻¹*(∫ x, x ∂(ρ : Measure ℝ)))
  have hbNonneg (i : Fin (n+k)) : 0 ≤ budget i := by
    induction i using Fin.addCases with
    | left i => simp only [budget,Fin.addCases_left,le_refl]
    | right j => simpa only [budget,Fin.addCases_right] using mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k)) hE
  have herror : ∀ i b, stopLoss (R.law i) b ≤ stopLoss (Q.law i) b+budget i := by
    intro i b
    induction i using Fin.addCases with
    | left i => simp only [Q,R,rareDesign,appendIID,Fin.addCases_left,budget,add_zero,le_refl]
    | right j =>
      have hb := (rareProbabilityLaw_stopLoss_add_bounds μ ρ H hμ hρ k (by exact_mod_cast hk) hm b).2
      simp only [NNReal.coe_natCast] at hb
      simp only [Q,R,rareDesign,appendIID,budget,Fin.addCases_right]
      linarith
  have hsum : (∑ i, budget i) = ∫ x, x ∂(ρ : Measure ℝ) := by
    rw [Fin.sum_univ_add]
    simp only [budget,Fin.addCases_left,Fin.addCases_right,Finset.sum_const_zero,zero_add,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hkR : (k : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hk)
    field_simp
  have hu := R.optimalScalarValue_le_of_stopLoss_error Q hR hQ budget hbNonneg herror hwP hc
  rw [hsum] at hu
  linarith

end ProphetSecretary.Limiting
