import ProphetSecretary.Limiting.RareDesignBenchmark
import ProphetSecretary.Limiting.HybridReserveShift
import ProphetSecretary.Limiting.HybridBenchmarkReserve
import ProphetSecretary.Model.TerminalScalarGap

/-!
# The global scalar inequality and reserve slack for finite-intensity hybrids

The finite rare design has a larger prophet benchmark than the Poisson law.
The proved all-policy finite inequality and the quantitative Poisson value
comparison therefore give the actual hybrid inequality. Exact reserve shifts
then give the positive terminal contribution without requiring M>0.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model
variable {n : ℕ}

lemma nnreal_le_bernoulliMultiplicity (R : ℝ≥0) (j : ℕ) :
    R ≤ (bernoulliMultiplicity (R : ℝ) j : ℝ≥0) := by
  have hceil := Nat.le_ceil (R : ℝ)
  have hn : Nat.ceil (R : ℝ) ≤ bernoulliMultiplicity (R : ℝ) j := by unfold bernoulliMultiplicity; omega
  exact_mod_cast hceil.trans (Nat.cast_le.mpr hn)

/-- The actual finite-intensity Poisson model satisfies the global scalar
comparison, including zero rate and zero expected maximum. -/
theorem FiniteIntensityHybridInstance.globalScalar_inequality_zero_terminal
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalCompetitiveRatio*(w*B.expectedMaximum+c) ≤ B.optimalScalarValue w c := by
  let W : ℝ≥0 := ⟨w,hw⟩
  let R := B.intensity.mass
  let ks := fun j => bernoulliMultiplicity (R : ℝ) j
  have hks (j : ℕ) : 0 < ks j := bernoulliMultiplicity_positive _ _
  have hkR (j : ℕ) : R ≤ (ks j : ℝ≥0) := nnreal_le_bernoulliMultiplicity R j
  let hμ : ∀ᵐ x ∂(B.intensity : Measure ℝ), x ∈ Icc (0 : ℝ) B.cap :=
    B.intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)
  let Qs := fun j => rareDesign B.individuals B.intensity B.cap hμ (ks j) (hks j) (hkR j)
  have hbound (j : ℕ) : optimalCompetitiveRatio*(w*B.expectedMaximum+c) ≤
      B.optimalScalarValue w c+rareDesignError B.cap W R (ks j) := by
    have hM := B.expectedMaximum_le_rareDesign ha (ks j) (hks j) (hkR j)
    have hglobal := Model.globalScalar_inequality (Qs j) B.cap.property
      (rareDesign_bounded B.individuals B.intensity B.cap B.individual_bounded hμ (ks j) (hks j) (hkR j)) hw hc
    have hcmp : optimalCompetitiveRatio*(w*B.expectedMaximum+c) ≤
        optimalCompetitiveRatio*(w*(Qs j).expectedMaximum+c) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hM hw) le_rfl)
        optimalCompetitiveRatio_nonnegative
    have herr := B.rareDesign_value_uniform_error ha W R le_rfl (ks j) (hks j) (hkR j) hw le_rfl hc
    have hV : Model.optimalScalarValue (Qs j) w c ≤
        B.optimalScalarValue w c+rareDesignError B.cap W R (ks j) := by
      have hh := (abs_le.mp herr).2
      linarith
    exact (hcmp.trans hglobal).trans hV
  have hlim : Tendsto (fun j => B.optimalScalarValue w c+rareDesignError B.cap W R (ks j)) atTop
      (𝓝 (B.optimalScalarValue w c)) := by
    simpa only [add_zero] using (rareDesignError_tendsto_zero B.cap W R).const_add (B.optimalScalarValue w c)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound)

noncomputable def FiniteIntensityHybridInstance.scalarGap (B : FiniteIntensityHybridInstance n) (w c : ℝ) : ℝ :=
  B.optimalScalarValue w c-optimalCompetitiveRatio*(w*B.expectedMaximum+c)

/-- Explicit reserve slack, uniform in retained dimension and every
nonnegative weight. No criticality or positive benchmark is assumed. -/
theorem FiniteIntensityHybridInstance.scalarGap_ge_terminal (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (1-optimalCompetitiveRatio)*w*(B.terminal : ℝ) ≤ B.scalarGap w c := by
  by_cases hw0 : w = 0
  · subst w
    unfold scalarGap
    rw [B.value_zero_rewardWeight hc]
    have h := mul_le_mul_of_nonneg_right optimalCompetitiveRatio_le_one hc
    simp only [mul_zero,zero_mul,zero_add,one_mul] at h ⊢
    linarith
  · have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    have hglobal := (B.excessState B.terminal).globalScalar_inequality_zero_terminal rfl hw hc
    unfold scalarGap
    rw [B.value_reserveShift hwP hc,B.expectedMaximum_reserveShift]
    nlinarith

lemma FiniteIntensityHybridInstance.scalarGap_nonnegative (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) : 0 ≤ B.scalarGap w c :=
  (mul_nonneg (mul_nonneg (sub_nonneg.mpr optimalCompetitiveRatio_le_one) hw) B.terminal.property).trans
    (B.scalarGap_ge_terminal hw hc)

end ProphetSecretary.Limiting
