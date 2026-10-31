import ProphetSecretary.Limiting.ScaledMarkNormalization
import ProphetSecretary.Limiting.HybridIntensityScale
import ProphetSecretary.Limiting.AppendIIDState
import ProphetSecretary.Limiting.HybridValueThreshold

/-!
# Uniform finite-Bernoulli state error at a remaining virtual count

The positive probability p=λ/q is fixed before the state is chosen. With K
unseen virtual identities, the matching hybrid intensity is (K/q)μ. The error
is bounded by the full-q Poisson approximation error, uniformly over K≤q and
every nonnegative duration coefficient. All virtual zero identities remain
part of the finite policy history.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma finitePoissonDesign_zero_rows (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval) : finitePoissonDesign P κ hκ p 0 = P := by
  apply Model.Instance.eq_of_law_eq
  funext i
  induction i using Fin.addCases with
  | left i =>
    simp only [finitePoissonDesign,appendIID,Fin.addCases_left]
    congr 1
  | right j => exact Fin.elim0 j

noncomputable def FiniteIntensityHybridInstance.bernoulliStateError (B : FiniteIntensityHybridInstance n)
    (w : ℝ) (j : ℕ) : ℝ :=
  let rate := (B.intensity : Measure ℝ).real univ
  let q := bernoulliMultiplicity rate j
  let p := bernoulliProbability rate measureReal_nonneg j
  (q : ℝ)*(w*(p : ℝ)^2*(B.cap : ℝ))+
    (Real.pi/2)*w*(B.cap : ℝ)*Real.sqrt ((q : ℝ)*(p : ℝ)^2)

lemma FiniteIntensityHybridInstance.bernoulliStateError_nonnegative (B : FiniteIntensityHybridInstance n)
    {w : ℝ} (hw : 0 ≤ w) (j : ℕ) : 0 ≤ B.bernoulliStateError w j := by
  unfold bernoulliStateError
  positivity

lemma FiniteIntensityHybridInstance.bernoulliStateError_tendsto_zero (B : FiniteIntensityHybridInstance n) (w : ℝ) :
    Tendsto (B.bernoulliStateError w) atTop (𝓝 0) :=
  bernoulliProbability_error_tendsto_zero ((B.intensity : Measure ℝ).real univ) measureReal_nonneg w B.cap

/-- The actual finite/hybrid state comparison. No positive benchmark is
required, and K=0 is the exact empty-virtual-family case. -/
theorem FiniteIntensityHybridInstance.finiteDesign_remaining_value_error
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    (j K : ℕ) (hK : K ≤ bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j)
    {w d : ℝ} (hw : 0 < w) (hd : 0 ≤ d) :
    let rate := (B.intensity : Measure ℝ).real univ
    let q := bernoulliMultiplicity rate j
    let p := bernoulliProbability rate measureReal_nonneg j
    let r : ℝ≥0 := (K : ℝ≥0)/(q : ℝ≥0)
    |Model.optimalScalarValue (finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ)
      (B.normalizedMark_nonnegative hμ) p K) w d-(B.remainingHorizon r).optimalScalarValue w d| ≤ B.bernoulliStateError w j := by
  dsimp only
  let rate := (B.intensity : Measure ℝ).real univ
  let q := bernoulliMultiplicity rate j
  let p := bernoulliProbability rate measureReal_nonneg j
  let r : ℝ≥0 := (K : ℝ≥0)/(q : ℝ≥0)
  let D := B.remainingHorizon r
  have hq : 0 < q := bernoulliMultiplicity_positive rate j
  by_cases hK0 : K = 0
  · subst K
    rw [finitePoissonDesign_zero_rows]
    have hD0 : D.intensity = 0 := by simp [D,r,FiniteIntensityHybridInstance.remainingHorizon]
    have hDV := D.value_zero_intensity ha hD0 hw.le hd
    change D.optimalScalarValue w d = Model.optimalScalarValue B.individuals w d at hDV
    rw [hDV,sub_self,abs_zero]
    exact B.bernoulliStateError_nonnegative hw.le j
  have hKP : 0 < K := Nat.pos_of_ne_zero hK0
  have hr : 0 < r := div_pos (by exact_mod_cast hKP) (by exact_mod_cast hq)
  have hD : D.intensity ≠ 0 := by
    change r • B.intensity ≠ 0
    rw [← FiniteMeasure.mass_nonzero_iff,finiteMeasure_mass_smul]
    exact mul_ne_zero hr.ne' (B.intensity.mass_nonzero_iff.mpr hμ)
  have hNorm : (D.intensity.normalize : Measure ℝ) = (B.intensity.normalize : Measure ℝ) := by
    calc
      _ = normalizedMarkOrZero D.intensity := by rw [normalizedMarkOrZero,if_neg hD]
      _ = normalizedMarkOrZero B.intensity := normalizedMarkOrZero_smul B.intensity hr
      _ = _ := by rw [normalizedMarkOrZero,if_neg hμ]
  have hRate : (D.intensity : Measure ℝ).real univ = (K : ℝ)*(p : ℝ) := by
    change (r • (B.intensity : Measure ℝ)).real univ = _
    rw [measureReal_nnreal_smul_apply]
    dsimp only [r,p,bernoulliProbability]
    rw [NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_natCast]
    ring
  have hFin : finitePoissonDesign D.individuals (D.intensity.normalize : Measure ℝ)
      (D.normalizedMark_nonnegative hD) p K =
      finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ)
        (B.normalizedMark_nonnegative hμ) p K := by
    apply Model.Instance.eq_of_law_eq
    funext i
    induction i using Fin.addCases with
    | left i => simp only [finitePoissonDesign,appendIID,Fin.addCases_left]; rfl
    | right i => simp only [finitePoissonDesign,appendIID,Fin.addCases_right,hNorm]
  have hCompare := D.BernoulliDesignValue_abs_difference_le ha hD p hRate hw hd
  dsimp only at hCompare
  rw [hFin,hNorm] at hCompare
  have hMH : (∫ x, x ∂(B.intensity.normalize : Measure ℝ)) ≤ (B.cap : ℝ) := by
    have hh := (normalized_ae B.intensity hμ B.intensity_supported).mono fun _ hx => hx.2
    simpa only [id_eq,integral_const,probReal_univ,one_smul] using
      integral_mono_ae (B.normalizedMark_integrable hμ) (integrable_const (B.cap : ℝ)) hh
  have hKq : (K : ℝ) ≤ (q : ℝ) := by exact_mod_cast hK
  have hSq : (K : ℝ)*(p : ℝ)^2 ≤ (q : ℝ)*(p : ℝ)^2 := mul_le_mul_of_nonneg_right hKq (sq_nonneg _)
  have hAux : (K : ℝ)*(p : ℝ)^2+(Real.pi/2)*Real.sqrt ((K : ℝ)*(p : ℝ)^2) ≤
      (q : ℝ)*(p : ℝ)^2+(Real.pi/2)*Real.sqrt ((q : ℝ)*(p : ℝ)^2) :=
    add_le_add hSq (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hSq) (by positivity))
  apply hCompare.trans
  calc
    _ = w*(∫ x, x ∂(B.intensity.normalize : Measure ℝ))*
        ((K : ℝ)*(p : ℝ)^2+(Real.pi/2)*Real.sqrt ((K : ℝ)*(p : ℝ)^2)) := by ring
    _ ≤ w*(B.cap : ℝ)*((K : ℝ)*(p : ℝ)^2+(Real.pi/2)*Real.sqrt ((K : ℝ)*(p : ℝ)^2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMH hw.le) (by positivity)
    _ ≤ w*(B.cap : ℝ)*((q : ℝ)*(p : ℝ)^2+(Real.pi/2)*Real.sqrt ((q : ℝ)*(p : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left hAux (by positivity)
    _ = B.bernoulliStateError w j := by unfold FiniteIntensityHybridInstance.bernoulliStateError; dsimp only [q,p,rate]; ring

end ProphetSecretary.Limiting
