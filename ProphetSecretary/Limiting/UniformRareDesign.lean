import ProphetSecretary.Limiting.FixedRareDesign

/-!
# Uniform fixed-size Poisson approximation

The explicit error uses only the common cap, a common total-intensity bound,
and a reward-weight bound. In particular it is uniform over all nonnegative
duration weights and does not depend on the retained instance dimension.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def rareDesignError (H W R : ℝ≥0) (k : ℕ) : ℝ :=
  (W : ℝ)*(H : ℝ)*((R : ℝ)^2/(k : ℝ)+(Real.pi/2)*Real.sqrt ((R : ℝ)^2/(k : ℝ)))

lemma rareDesignError_tendsto_zero (H W R : ℝ≥0) :
    Tendsto (fun j => rareDesignError H W R (bernoulliMultiplicity (R : ℝ) j)) atTop (𝓝 0) := by
  have hs : Tendsto (fun j => (R : ℝ)^2/(bernoulliMultiplicity (R : ℝ) j : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (bernoulliMultiplicity_tendsto_atTop R)
  have h := (hs.add ((Real.continuous_sqrt.tendsto 0 |>.comp hs).const_mul (Real.pi/2))).const_mul ((W : ℝ)*(H : ℝ))
  simpa only [rareDesignError,Function.comp_apply,Real.sqrt_zero,mul_zero,add_zero] using h

/-- Uniformity is quantitative before limits are taken. Zero intensity and
zero reward weight are included. -/
theorem FiniteIntensityHybridInstance.rareDesign_value_uniform_error
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    (W R : ℝ≥0) (hrate : B.intensity.mass ≤ R)
    (k : ℕ) (hk : 0 < k) (hkR : R ≤ (k : ℝ≥0))
    {w c : ℝ} (hw : 0 ≤ w) (hwW : w ≤ (W : ℝ)) (hc : 0 ≤ c) :
    |Model.optimalScalarValue (rareDesign B.individuals B.intensity B.cap
      (B.intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2⟩) k hk (hrate.trans hkR)) w c - B.optimalScalarValue w c| ≤
      rareDesignError B.cap W R k := by
  let p := rareParameter B.intensity (k : ℝ≥0) (by exact_mod_cast hk) (hrate.trans hkR)
  have hkP : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hM : (B.intensity.mass : ℝ) ≤ (R : ℝ) := by exact_mod_cast hrate
  have hs : (k : ℝ)*(p : ℝ)^2 ≤ (R : ℝ)^2/(k : ℝ) := by
    have he : (k : ℝ)*(p : ℝ) = (B.intensity.mass : ℝ) :=
      (rareParameter_total B.intensity k (by exact_mod_cast hk) (hrate.trans hkR)).symm
    have hsq : (B.intensity.mass : ℝ)^2 ≤ (R : ℝ)^2 := by nlinarith [B.intensity.mass.coe_nonneg]
    apply (le_div_iff₀ hkP).mpr
    calc
      _ = ((k : ℝ)*(p : ℝ))^2 := by ring
      _ = (B.intensity.mass : ℝ)^2 := by rw [he]
      _ ≤ (R : ℝ)^2 := hsq
  have hsmall : 0 ≤ (k : ℝ)*(p : ℝ)^2+(Real.pi/2)*Real.sqrt ((k : ℝ)*(p : ℝ)^2) := by positivity
  have hbig : (k : ℝ)*(p : ℝ)^2+(Real.pi/2)*Real.sqrt ((k : ℝ)*(p : ℝ)^2) ≤
      (R : ℝ)^2/(k : ℝ)+(Real.pi/2)*Real.sqrt ((R : ℝ)^2/(k : ℝ)) :=
    add_le_add hs (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs) (by positivity))
  have hb := B.rareDesign_value_error ha k hk (hrate.trans hkR) hw hc
  calc
    _ ≤ (k : ℝ)*(w*(p : ℝ)^2*(B.cap : ℝ))+
        (Real.pi/2)*w*(B.cap : ℝ)*Real.sqrt ((k : ℝ)*(p : ℝ)^2) := hb
    _ = w*(B.cap : ℝ)*((k : ℝ)*(p : ℝ)^2+(Real.pi/2)*Real.sqrt ((k : ℝ)*(p : ℝ)^2)) := by ring
    _ ≤ (W : ℝ)*(B.cap : ℝ)*((k : ℝ)*(p : ℝ)^2+(Real.pi/2)*Real.sqrt ((k : ℝ)*(p : ℝ)^2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwW B.cap.property) hsmall
    _ ≤ rareDesignError B.cap W R k := mul_le_mul_of_nonneg_left hbig (by positivity)

end ProphetSecretary.Limiting
