import ProphetSecretary.Stability.LawRegretRegularity

/-!
# Exact score response and elimination of reward terms

The policy remains fixed at the base law. Complete scores may depend on values
arriving after stopping; all expectations here are analytical derivatives,
not observations supplied to the policy. `updual:elimination` is an exact identity.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

noncomputable def RandomizedPolicy.expectedRewardScore (π : RandomizedPolicy n) (P : Instance n)
    (h : Fin n → ℝ → ℝ) : ℝ :=
  ∫ ω : π.World, completeScore h ω.1 * π.realizedReward ω ∂P.worldLaw π.seedLaw
noncomputable def RandomizedPolicy.expectedDurationScore (π : RandomizedPolicy n) (P : Instance n)
    (h : Fin n → ℝ → ℝ) : ℝ :=
  ∫ ω : π.World, completeScore h ω.1 * π.realizedDuration ω ∂P.worldLaw π.seedLaw
noncomputable def Instance.expectedMaximumScore (P : Instance n) (h : Fin n → ℝ → ℝ) : ℝ :=
  ∫ x, completeScore h x * Instance.maximum x ∂P.valuesLaw
noncomputable def RandomizedPolicy.normalizedScoreResponse (π : RandomizedPolicy n) (P : Instance n)
    (h : Fin n → ℝ → ℝ) (lam : ℝ) : ℝ :=
  lam * (π.expectedRewardScore P h - optimalCompetitiveRatio * P.expectedMaximumScore h) +
    (1-lam) * π.expectedDurationScore P h

lemma RandomizedPolicy.scalarLikelihoodDerivative_eq_scores (π : RandomizedPolicy n) (P : Instance n)
    {H : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (w c : ℝ) :
    π.scalarLikelihoodDerivative P w c h = w * π.expectedRewardScore P h + c * π.expectedDurationScore P h := by
  have hR : Integrable (fun ω : π.World => completeScore h ω.1 * π.realizedReward ω) (P.worldLaw π.seedLaw) := by
    simpa only [one_mul,zero_mul,add_zero,mul_comm] using
      π.integrable_scalarScore_of_bounded P hH hbound zero_le_one (le_refl 0) h hh hb
  have hT : Integrable (fun ω : π.World => completeScore h ω.1 * π.realizedDuration ω) (P.worldLaw π.seedLaw) := by
    simpa only [one_mul,zero_mul,zero_add,mul_comm] using
      π.integrable_scalarScore_of_bounded P hH hbound (le_refl 0) zero_le_one h hh hb
  unfold scalarLikelihoodDerivative expectedRewardScore expectedDurationScore
  have heq : (fun ω : π.World => (w * π.realizedReward ω + c * π.realizedDuration ω) * completeScore h ω.1) =
      fun ω => w * (completeScore h ω.1 * π.realizedReward ω) + c * (completeScore h ω.1 * π.realizedDuration ω) := by
    funext ω
    ring
  rw [heq,integral_add (hR.const_mul w) (hT.const_mul c),integral_const_mul,integral_const_mul]

lemma RandomizedPolicy.hasDerivAt_scalarObjective_likelihoodWidePath_zero (π : RandomizedPolicy n)
    (P : Instance n) {H w c : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (hw : 0 ≤ w) (hc : 0 ≤ c) (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) :
    HasDerivAt (fun t => π.scalarObjective (P.likelihoodWidePath h hh hb hm t) w c)
      (π.scalarLikelihoodDerivative P w c h) 0 := by
  apply (π.hasDerivAt_scalarObjective_likelihoodPath P hH hbound hw hc h hh hb hm).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (by norm_num : -(1/4 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1/4)] with t ht
  rw [P.likelihoodWidePath_eq_quarter h hh hb hm (abs_le.mpr ht)]

lemma Instance.hasDerivAt_expectedMaximum_likelihoodWidePath_zero (P : Instance n) {H : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) :
    HasDerivAt (fun t => (P.likelihoodWidePath h hh hb hm t).expectedMaximum) (P.expectedMaximumScore h) 0 := by
  have hFb : ∀ᵐ x ∂P.valuesLaw, |Instance.maximum x| ≤ H :=
    (P.values_bound_ae hbound).mono fun x hx => by
      rw [abs_of_nonneg (Instance.maximum_nonnegative x)]
      exact Instance.maximum_le x hH hx
  have hd := hasDerivAt_fixedPayoff_law_zero P.law h hh hb hm Instance.maximum
    Instance.measurable_maximum hH hFb
  have hd' : HasDerivAt (fun t => ∫ x, Instance.maximum x ∂productTiltLaw P.law h t) (P.expectedMaximumScore h) 0 := by
    convert hd using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => mul_comm _ _
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (by norm_num : -(1/4 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1/4)] with t ht
  rw [P.likelihoodWidePath_eq_quarter h hh hb hm (abs_le.mpr ht), P.likelihoodPath_of_mem h hh hb hm (abs_le.mpr ht)]
  rfl

/-- The product-score identity in `updual:derivative`, with the policy fixed. -/
theorem RandomizedPolicy.hasDerivAt_normalizedScoreResponse (π : RandomizedPolicy n) (P : Instance n)
    {H lam : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) :
    HasDerivAt (fun t => π.scalarObjective (P.likelihoodWidePath h hh hb hm t) lam (1-lam) -
      optimalCompetitiveRatio * (lam * (P.likelihoodWidePath h hh hb hm t).expectedMaximum + 1-lam))
      (π.normalizedScoreResponse P h lam) 0 := by
  have hJ := π.hasDerivAt_scalarObjective_likelihoodWidePath_zero P hH hbound hlam.1 (sub_nonneg.mpr hlam.2) h hh hb hm
  have hM := P.hasDerivAt_expectedMaximum_likelihoodWidePath_zero hH hbound h hh hb hm
  have hd := hJ.sub (((hM.const_mul lam).add_const (1-lam)).const_mul optimalCompetitiveRatio)
  rw [π.scalarLikelihoodDerivative_eq_scores P hH hbound h hh hb] at hd
  convert hd using 1
  all_goals first | rfl | (unfold normalizedScoreResponse; ring) | (funext t; dsimp; ring)

/-- Exact score elimination `updual:elimination`; no response nondegeneracy
or lower bound on the duration score is assumed. -/
theorem RandomizedPolicy.normalizedScoreResponse_elimination (π : RandomizedPolicy n) (P : Instance n)
    (h : Fin n → ℝ → ℝ) (lam₁ lam₂ : ℝ) :
    (lam₂-lam₁) * π.expectedDurationScore P h =
      lam₂ * π.normalizedScoreResponse P h lam₁ - lam₁ * π.normalizedScoreResponse P h lam₂ := by
  unfold normalizedScoreResponse
  ring

end ProphetSecretary.Model
