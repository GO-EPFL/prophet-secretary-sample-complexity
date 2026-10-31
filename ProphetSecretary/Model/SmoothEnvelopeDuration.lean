import ProphetSecretary.Stability.LawGapRegretSlope

/-!
# The finite smooth-envelope duration-response inequality

This assembles `updual:endpointregret`, `updual:derivative` and
`updual:elimination` for an actual midpoint optimizer. The explicit constant
is independent of n, the marginal laws and the score direction. No lower
bound on the duration response is assumed here; nondegeneracy and limiting
score transfer remain separate mathematical obligations.
-/
open MeasureTheory Set
open scoped Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability ProphetSecretary.Analysis
variable {n : ℕ}

noncomputable def smoothEnvelopeDurationConstant (H S₀ δ I₀ : ℝ) : ℝ :=
  4 * smoothEnvelopeSlopeConstant H S₀ δ I₀

lemma RandomizedPolicy.normalizedScoreResponse_eq_gap_sub_regret_deriv (π : RandomizedPolicy n)
    (P : Instance n) {H lam : ℝ} (hH : 0 ≤ H) (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    π.normalizedScoreResponse P h lam =
      deriv (fun t => normalizedScalarGap (P.likelihoodWidePath h hh hb hm t) lam) 0 -
      deriv (fun t => π.normalizedRegret (P.likelihoodWidePath h hh hb hm t) lam) 0 := by
  have hz : (0 : ℝ) ∈ Icc (-(1/4) : ℝ) (1/4) := by norm_num
  rw [P.deriv_normalizedScalarGap_likelihoodWidePath hH hlam hbound h hh hb hm hz,
    (π.hasDerivAt_normalizedRegret_likelihoodWidePath P hH hlam hbound h hh hb hm hz).deriv,
    (P.hasDerivAt_expectedMaximum_likelihoodWidePath_zero hH hbound h hh hb hm).deriv,
    (π.hasDerivAt_scalarObjective_likelihoodWidePath_zero P hH hbound hlam.1.le (sub_nonneg.mpr hlam.2.le) h hh hb hm).deriv,
    π.scalarLikelihoodDerivative_eq_scores P hH hbound h hh hb]
  unfold normalizedScoreResponse
  ring

/-- Uniform finite score-response inequality, for every fixed midpoint
optimizer among general admissible policies. -/
theorem RandomizedPolicy.midpoint_durationScore_separation_bound (π : RandomizedPolicy n) (P : Instance n)
    {H S₀ δ I₀ lam₁ lam₂ : ℝ} (hH : 0 ≤ H) (hS₀ : 0 ≤ S₀) (hδ : 0 < δ) (hI₀ : 0 ≤ I₀)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hS : P.totalFirstMoment ≤ S₀)
    (hlam₁ : lam₁ ∈ Icc δ (1-δ)) (hlam₂ : lam₂ ∈ Icc δ (1-δ))
    (hopt : π.scalarObjective P ((lam₁+lam₂)/2) (1-(lam₁+lam₂)/2) =
      optimalScalarValue P ((lam₁+lam₂)/2) (1-(lam₁+lam₂)/2))
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (hInfo : information P.law h ≤ I₀) :
    |lam₂-lam₁| * |π.expectedDurationScore P h| ≤
      smoothEnvelopeDurationConstant H S₀ δ I₀ * Real.sqrt (normalizedScalarGap P lam₁ + normalizedScalarGap P lam₂) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hLam₁ : lam₁ ∈ Ioo (0 : ℝ) 1 := ⟨hδ.trans_le hlam₁.1,by linarith [hlam₁.2]⟩
  have hLam₂ : lam₂ ∈ Ioo (0 : ℝ) 1 := ⟨hδ.trans_le hlam₂.1,by linarith [hlam₂.2]⟩
  have hLam₁01 : lam₁ ∈ Icc (0 : ℝ) 1 := ⟨hLam₁.1.le,hLam₁.2.le⟩
  have hLam₂01 : lam₂ ∈ Icc (0 : ℝ) 1 := ⟨hLam₂.1.le,hLam₂.2.le⟩
  let s := normalizedScalarGap P lam₁ + normalizedScalarGap P lam₂
  let D := smoothEnvelopeSlopeConstant H S₀ δ I₀
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hr := π.midpoint_endpointRegrets P hP hLam₁01 hLam₂01 hopt
  have hf₁ := normalizedScalarGap_nonnegative P hP hLam₁01
  have hf₂ := normalizedScalarGap_nonnegative P hP hLam₂01
  have hd (lam : ℝ) (hlam : lam ∈ Icc δ (1-δ))
      (hLam : lam ∈ Ioo (0 : ℝ) 1)
      (hF : normalizedScalarGap P lam ≤ s) (hr : π.normalizedRegret P lam ≤ s) :
      |π.normalizedScoreResponse P h lam| ≤ 2 * D * Real.sqrt s := by
    have hbds := π.lawGap_regret_derivative_sqrt_bounds P hH hS₀ hδ hI₀ hlam hbound hS h hh hb hm hInfo
    rw [π.normalizedScoreResponse_eq_gap_sub_regret_deriv P hH hLam hbound h hh hb hm]
    apply (abs_sub _ _).trans
    have hF' := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hF) hD
    have hr' := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr) hD
    change _ ≤ 2 * D * Real.sqrt s
    nlinarith only [hbds.1,hbds.2,hF',hr']
  have hd₁ := hd lam₁ hlam₁ hLam₁ (by dsimp [s]; linarith only [hf₂]) hr.2.2.1
  have hd₂ := hd lam₂ hlam₂ hLam₂ (by dsimp [s]; linarith only [hf₁]) hr.2.2.2
  rw [← abs_mul,π.normalizedScoreResponse_elimination P h lam₁ lam₂]
  calc
    _ ≤ |lam₂ * π.normalizedScoreResponse P h lam₁| + |lam₁ * π.normalizedScoreResponse P h lam₂| := abs_sub _ _
    _ = lam₂ * |π.normalizedScoreResponse P h lam₁| + lam₁ * |π.normalizedScoreResponse P h lam₂| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hLam₁01.1,abs_of_nonneg hLam₂01.1]
    _ ≤ |π.normalizedScoreResponse P h lam₁| + |π.normalizedScoreResponse P h lam₂| :=
      add_le_add (mul_le_of_le_one_left (abs_nonneg _) hLam₂01.2) (mul_le_of_le_one_left (abs_nonneg _) hLam₁01.2)
    _ ≤ _ := by change _ ≤ 4 * D * Real.sqrt s; linarith only [hd₁,hd₂]

/-- Actual canonical-midpoint specialization of the finite smooth-envelope
inequality, before any nonzero-response or compactness argument. -/
theorem Instance.canonical_midpoint_durationScore_separation_bound (P : Instance n)
    {H S₀ δ I₀ lam₁ lam₂ : ℝ} (hH : 0 ≤ H) (hS₀ : 0 ≤ S₀) (hδ : 0 < δ) (hI₀ : 0 ≤ I₀)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hS : P.totalFirstMoment ≤ S₀)
    (hlam₁ : lam₁ ∈ Icc δ (1-δ)) (hlam₂ : lam₂ ∈ Icc δ (1-δ))
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (hInfo : information P.law h ≤ I₀) :
    let hP := P.integrable_maximum_of_bounded hbound
    let hw : 0 < (lam₁+lam₂)/2 := by linarith [hlam₁.1,hlam₂.1]
    let hc : 0 ≤ 1-(lam₁+lam₂)/2 := by linarith [hlam₁.2,hlam₂.2]
    let π := P.valuePolicy hP hw.le hc
    |lam₂-lam₁| * |π.expectedDurationScore P h| ≤
      smoothEnvelopeDurationConstant H S₀ δ I₀ * Real.sqrt (normalizedScalarGap P lam₁ + normalizedScalarGap P lam₂) := by
  dsimp only
  apply RandomizedPolicy.midpoint_durationScore_separation_bound _ P hH hS₀ hδ hI₀ hbound hS hlam₁ hlam₂
    (P.valuePolicy_optimal _ (by linarith [hlam₁.1,hlam₂.1]) (by linarith [hlam₁.2,hlam₂.2])) h hh hb hm hInfo

end ProphetSecretary.Model
