import ProphetSecretary.Limiting.RareMarginalPositivePart
import ProphetSecretary.Limiting.FinitePoissonApproximation

/-!
# Fixed-size finite rare designs

The number of virtual offers is fixed independently of the intensity law.
Consequently its probability marginals have weak limits even at zero rate.
The approximation estimate is inherited from the actual Poisson comparison.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def rareDesign (P : Model.Instance n) (μ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (k : ℕ) (hk : 0 < k) (hm : μ.mass ≤ (k : ℝ≥0)) : Model.Instance (n+k) :=
  appendIID P (rareProbabilityLaw μ k (by exact_mod_cast hk) hm : Measure ℝ)
    ((rareProbabilityLaw_bounds μ H hμ k (by exact_mod_cast hk) hm).mono fun _ hx => hx.1) k

lemma rareDesign_eq_zeroInflated (P : Model.Instance n) (μ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (k : ℕ) (hk : 0 < k) (hm : μ.mass ≤ (k : ℝ≥0))
    (hκ : ∀ᵐ x ∂normalizedMarkOrZero μ, 0 ≤ x) :
    rareDesign P μ H hμ k hk hm = finitePoissonDesign P (normalizedMarkOrZero μ) hκ
      (rareParameter μ k (by exact_mod_cast hk) hm) k := by
  apply Model.Instance.eq_of_law_eq
  funext i
  induction i using Fin.addCases with
  | left i => simp only [rareDesign,finitePoissonDesign,appendIID,Fin.addCases_left]
  | right j =>
    simp only [rareDesign,finitePoissonDesign,appendIID,Fin.addCases_right]
    exact rareProbabilityLaw_eq_zeroInflated μ k (by exact_mod_cast hk) hm

lemma rareDesign_zero (P : Model.Instance n) (H : ℝ≥0)
    (hμ : ∀ᵐ x ∂((0 : FiniteMeasure ℝ) : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (k : ℕ) (hk : 0 < k) (hm : (0 : FiniteMeasure ℝ).mass ≤ (k : ℝ≥0)) :
    rareDesign P 0 H hμ k hk hm = P.appendZeros k := by
  rw [rareDesign_eq_zeroInflated P 0 H hμ k hk hm (by simp [normalizedMarkOrZero])]
  have hp : rareParameter 0 (k : ℝ≥0) (by exact_mod_cast hk) hm = 0 := by
    apply Subtype.ext
    simp [rareParameter]
  rw [hp,finitePoissonDesign_probability_zero]

lemma FiniteIntensityHybridInstance.value_zero_rewardWeight (B : FiniteIntensityHybridInstance n)
    {c : ℝ} (hc : 0 ≤ c) : B.optimalScalarValue 0 c = c := by
  exact le_antisymm (by simpa using B.optimalScalarValue_le (show (0 : ℝ) ≤ 0 from le_rfl) hc)
    (B.durationReward_le_optimalScalarValue le_rfl)

/-- Fixed-size approximation with the actual rate, before any bound on that
rate is substituted. The terminal reward is zero in this comparison. -/
theorem FiniteIntensityHybridInstance.rareDesign_value_error
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    (k : ℕ) (hk : 0 < k) (hm : B.intensity.mass ≤ (k : ℝ≥0))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    let hμ := B.intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)
    let p := rareParameter B.intensity (k : ℝ≥0) (by exact_mod_cast hk) hm
    |Model.optimalScalarValue (rareDesign B.individuals B.intensity B.cap hμ k hk hm) w c - B.optimalScalarValue w c| ≤
      (k : ℝ)*(w*(p : ℝ)^2*(B.cap : ℝ)) +
        (Real.pi/2)*w*(B.cap : ℝ)*Real.sqrt ((k : ℝ)*(p : ℝ)^2) := by
  dsimp only
  by_cases hw0 : w = 0
  · subst w
    rw [Model.optimalScalarValue_zero_rewardWeight _ hc,B.value_zero_rewardWeight hc]
    simp
  have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  by_cases hμ0 : B.intensity = 0
  · have he : rareDesign B.individuals B.intensity B.cap
        (B.intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)) k hk hm = B.individuals.appendZeros k := by
      simpa only [hμ0] using rareDesign_zero B.individuals B.cap (by simp) k hk (by simp)
    rw [he,B.individuals.optimalScalarValue_appendZeros k
      (B.individuals.integrable_maximum_of_bounded B.individual_bounded) hw hc,
      B.value_zero_intensity ha hμ0 hw hc]
    simp only [sub_self,abs_zero]
    positivity
  · have hs : ∀ᵐ x ∂(B.intensity.normalize : Measure ℝ), x ≤ (B.cap : ℝ) :=
      (normalized_ae B.intensity hμ0 B.intensity_supported).mono fun _ hx => hx.2
    have hM : (∫ x, x ∂(B.intensity.normalize : Measure ℝ)) ≤ (B.cap : ℝ) := by
      simpa only [id_eq,integral_const,probReal_univ,one_smul] using
        integral_mono_ae (B.normalizedMark_integrable hμ0) (integrable_const (B.cap : ℝ)) hs
    have he := rareDesign_eq_zeroInflated B.individuals B.intensity B.cap
      (B.intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)) k hk hm
      ((normalizedMarkOrZero_bounds B.intensity B.cap.property B.intensity_supported).mono fun _ hx => hx.1)
    have hκ : normalizedMarkOrZero B.intensity = (B.intensity.normalize : Measure ℝ) := by
      simp only [normalizedMarkOrZero,if_neg hμ0]
    have he' : rareDesign B.individuals B.intensity B.cap
        (B.intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)) k hk hm =
        finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ0)
          (rareParameter B.intensity k (by exact_mod_cast hk) hm) k := by
      apply Model.Instance.eq_of_law_eq
      funext i
      rw [he]
      induction i using Fin.addCases with
      | left i => simp only [finitePoissonDesign,appendIID,Fin.addCases_left]
      | right j => simp only [finitePoissonDesign,appendIID,Fin.addCases_right,hκ]
    rw [he']
    apply (B.BernoulliDesignValue_abs_difference_le ha hμ0
      (rareParameter B.intensity k (by exact_mod_cast hk) hm)
      (rareParameter_total B.intensity k (by exact_mod_cast hk) hm) hwP hc).trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM (mul_nonneg hw (sq_nonneg _))) (Nat.cast_nonneg _)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (mul_nonneg (by positivity) hw)) (Real.sqrt_nonneg _)

end ProphetSecretary.Limiting
