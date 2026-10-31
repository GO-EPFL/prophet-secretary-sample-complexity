import ProphetSecretary.Probability.PoissonLikelihoodBounds
import ProphetSecretary.Probability.PoissonLikelihoodMoments
import ProphetSecretary.Probability.LikelihoodRemainder

/-!
# Differentiating a fixed bounded payoff under a Poisson likelihood

The payoff and its underlying probability law remain fixed. A measurable count
has its actual Poisson law; no independence between the count and payoff is
required. Geometric moment bounds justify differentiation under the integral.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def poissonPayoffMean (μ : Measure Ω) (rate : ℝ≥0) (N : Ω → ℕ)
    (F : Ω → ℝ) (θ : ℝ) : ℝ := ∫ x, F x*poissonLikelihood rate θ (N x) ∂μ

noncomputable def poissonPayoffFirst (μ : Measure Ω) (rate : ℝ≥0) (N : Ω → ℕ)
    (F : Ω → ℝ) (θ : ℝ) : ℝ := ∫ x, F x*poissonLikelihoodFirst rate θ (N x) ∂μ

noncomputable def poissonPayoffSecond (μ : Measure Ω) (rate : ℝ≥0) (N : Ω → ℕ)
    (F : Ω → ℝ) (θ : ℝ) : ℝ := ∫ x, F x*poissonLikelihoodSecond rate θ (N x) ∂μ

lemma poissonPayoff_integrable_local (μ : Measure Ω) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    (N : Ω → ℕ) (hN : Measurable N) (hLaw : HasLaw N (poissonMeasure rate) μ)
    (F : Ω → ℝ) (hF : Measurable F) {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ᵐ x ∂μ, |F x| ≤ C) {θ : ℝ} (hθ : |θ| ≤ 1/2) :
    Integrable (fun x => F x*poissonLikelihood rate θ (N x)) μ ∧
    Integrable (fun x => F x*poissonLikelihoodFirst rate θ (N x)) μ ∧
    Integrable (fun x => F x*poissonLikelihoodSecond rate θ (N x)) μ := by
  have hMP : MeasurePreserving N μ (poissonMeasure rate) := ⟨hN,hLaw.map_eq⟩
  let a : ℝ≥0 := ⟨3/2,by norm_num⟩
  have hG0 : Integrable (fun x => Real.exp ((rate : ℝ)/2)*(3/2 : ℝ)^(N x)) μ :=
    hMP.integrable_comp_of_integrable ((integrable_poisson_geometric_zero rate a).const_mul (Real.exp ((rate : ℝ)/2)))
  have hG1 : Integrable (fun x => Real.exp ((rate : ℝ)/2)*(3/2 : ℝ)^(N x)*(2*(N x : ℝ)+(rate : ℝ))) μ :=
    hMP.integrable_comp_of_integrable (integrable_poisson_firstEnvelope rate)
  have hG2 : Integrable (fun x => Real.exp ((rate : ℝ)/2)*(3/2 : ℝ)^(N x)*((2*(N x : ℝ)+(rate : ℝ))^2+4*(N x : ℝ))) μ :=
    hMP.integrable_comp_of_integrable (integrable_poisson_secondEnvelope rate)
  constructor
  · apply (hG0.const_mul C).mono'
      (hF.mul ((measurable_of_countable (poissonLikelihood rate θ)).comp hN)).aestronglyMeasurable
    filter_upwards [hBound] with x hx
    simp only [Pi.mul_apply,Function.comp_apply,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul hx (poissonLikelihood_local_bounds rate (N x) hθ).1 (abs_nonneg _) hC
  constructor
  · apply (hG1.const_mul C).mono'
      (hF.mul ((measurable_of_countable (poissonLikelihoodFirst rate θ)).comp hN)).aestronglyMeasurable
    filter_upwards [hBound] with x hx
    simp only [Pi.mul_apply,Function.comp_apply,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul hx (poissonLikelihood_local_bounds rate (N x) hθ).2.1 (abs_nonneg _) hC
  · apply (hG2.const_mul C).mono'
      (hF.mul ((measurable_of_countable (poissonLikelihoodSecond rate θ)).comp hN)).aestronglyMeasurable
    filter_upwards [hBound] with x hx
    simp only [Pi.mul_apply,Function.comp_apply,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul hx (poissonLikelihood_local_bounds rate (N x) hθ).2.2 (abs_nonneg _) hC

lemma poissonPayoff_derivatives (μ : Measure Ω) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    (N : Ω → ℕ) (hN : Measurable N) (hLaw : HasLaw N (poissonMeasure rate) μ)
    (F : Ω → ℝ) (hF : Measurable F) {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ᵐ x ∂μ, |F x| ≤ C) {θ₀ : ℝ} (hθ₀ : |θ₀| ≤ 1/4) :
    HasDerivAt (poissonPayoffMean μ rate N F) (poissonPayoffFirst μ rate N F θ₀) θ₀ ∧
    HasDerivAt (poissonPayoffFirst μ rate N F) (poissonPayoffSecond μ rate N F θ₀) θ₀ := by
  have hMP : MeasurePreserving N μ (poissonMeasure rate) := ⟨hN,hLaw.map_eq⟩
  have hi := poissonPayoff_integrable_local μ rate N hN hLaw F hF hC hBound
    (hθ₀.trans (by norm_num : (1/4 : ℝ) ≤ 1/2))
  have hs : Ioo (-(1/2 : ℝ)) (1/2) ∈ 𝓝 θ₀ := by
    have h := abs_le.mp hθ₀
    exact Ioo_mem_nhds (by linarith) (by linarith)
  have hHalf (t : ℝ) (ht : t ∈ Ioo (-(1/2 : ℝ)) (1/2)) : |t| ≤ 1/2 :=
    abs_le.mpr ⟨ht.1.le,ht.2.le⟩
  have hPositive (t : ℝ) (ht : t ∈ Ioo (-(1/2 : ℝ)) (1/2)) : 0 < 1+t := by linarith only [ht.1]
  have hG1 : Integrable (fun x => C*(Real.exp ((rate : ℝ)/2)*(3/2 : ℝ)^(N x)*(2*(N x : ℝ)+(rate : ℝ)))) μ :=
    (hMP.integrable_comp_of_integrable (integrable_poisson_firstEnvelope rate)).const_mul C
  have hG2 : Integrable (fun x => C*(Real.exp ((rate : ℝ)/2)*(3/2 : ℝ)^(N x)*((2*(N x : ℝ)+(rate : ℝ))^2+4*(N x : ℝ)))) μ :=
    (hMP.integrable_comp_of_integrable (integrable_poisson_secondEnvelope rate)).const_mul C
  constructor
  · have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := fun t x => F x*poissonLikelihood rate t (N x))
      (F' := fun t x => F x*poissonLikelihoodFirst rate t (N x))
      (bound := fun x => C*(Real.exp ((rate : ℝ)/2)*(3/2 : ℝ)^(N x)*(2*(N x : ℝ)+(rate : ℝ)))) hs
      (Eventually.of_forall (fun t => (hF.mul ((measurable_of_countable (poissonLikelihood rate t)).comp hN)).aestronglyMeasurable))
      hi.1 (hF.mul ((measurable_of_countable (poissonLikelihoodFirst rate θ₀)).comp hN)).aestronglyMeasurable
      (by
        filter_upwards [hBound] with x hx
        intro t ht
        rw [Real.norm_eq_abs,abs_mul]
        exact mul_le_mul hx (poissonLikelihood_local_bounds rate (N x) (hHalf t ht)).2.1 (abs_nonneg _) hC)
      hG1 (Eventually.of_forall (fun x t ht =>
        (hasDerivAt_poissonLikelihood rate t (N x) (hPositive t ht)).const_mul (F x)))
    exact hd.2
  · have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := fun t x => F x*poissonLikelihoodFirst rate t (N x))
      (F' := fun t x => F x*poissonLikelihoodSecond rate t (N x))
      (bound := fun x => C*(Real.exp ((rate : ℝ)/2)*(3/2 : ℝ)^(N x)*((2*(N x : ℝ)+(rate : ℝ))^2+4*(N x : ℝ)))) hs
      (Eventually.of_forall (fun t => (hF.mul ((measurable_of_countable (poissonLikelihoodFirst rate t)).comp hN)).aestronglyMeasurable))
      hi.2.1 (hF.mul ((measurable_of_countable (poissonLikelihoodSecond rate θ₀)).comp hN)).aestronglyMeasurable
      (by
        filter_upwards [hBound] with x hx
        intro t ht
        rw [Real.norm_eq_abs,abs_mul]
        exact mul_le_mul hx (poissonLikelihood_local_bounds rate (N x) (hHalf t ht)).2.2 (abs_nonneg _) hC)
      hG2 (Eventually.of_forall (fun x t ht =>
        (hasDerivAt_poissonLikelihoodFirst rate t (N x) (hPositive t ht)).const_mul (F x)))
    exact hd.2

lemma measurable_poissonPayoffSecond (μ : Measure Ω) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    (N : Ω → ℕ) (hN : Measurable N) (F : Ω → ℝ) (hF : Measurable F) :
    Measurable (poissonPayoffSecond μ rate N F) := by
  have hJoint : Measurable (fun z : ℝ × Ω => F z.2*poissonLikelihoodSecond rate z.1 (N z.2)) :=
    (hF.comp measurable_snd).mul ((measurable_poissonLikelihoodSecond_joint rate).comp
      (measurable_fst.prodMk (hN.comp measurable_snd)))
  exact hJoint.stronglyMeasurable.integral_prod_right'.measurable

lemma poissonPayoffSecond_abs_le (μ : Measure Ω) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    (N : Ω → ℕ) (hN : Measurable N) (hLaw : HasLaw N (poissonMeasure rate) μ)
    (F : Ω → ℝ) (hF : Measurable F) {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ᵐ x ∂μ, |F x| ≤ C) {θ : ℝ} (hθ : |θ| ≤ 1/4) :
    |poissonPayoffSecond μ rate N F θ| ≤ 4*C*(rate : ℝ) := by
  have hHalf := hθ.trans (by norm_num : (1/4 : ℝ) ≤ 1/2)
  have hi := (poissonPayoff_integrable_local μ rate N hN hLaw F hF hC hBound hHalf).2.2
  have hMP : MeasurePreserving N μ (poissonMeasure rate) := ⟨hN,hLaw.map_eq⟩
  have hPos : 0 < 1+θ := by have h := (abs_le.mp hHalf).1; linarith only [h]
  have hZI : Integrable (fun x => poissonLikelihoodSecond rate θ (N x)) μ :=
    hMP.integrable_comp_of_integrable (poissonLikelihoodSecond_integrable_and_bound rate hPos).1
  have hIntegral := hLaw.integral_comp
    ((measurable_of_countable (fun n : ℕ => |poissonLikelihoodSecond rate θ n|))).aestronglyMeasurable
  calc
    _ ≤ ∫ x, |F x*poissonLikelihoodSecond rate θ (N x)| ∂μ := by
      simpa only [poissonPayoffSecond,Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => F x*poissonLikelihoodSecond rate θ (N x))
    _ ≤ ∫ x, C*|poissonLikelihoodSecond rate θ (N x)| ∂μ := by
      apply integral_mono_ae hi.abs (hZI.abs.const_mul C)
      filter_upwards [hBound] with x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ = C*(∫ x, |poissonLikelihoodSecond rate θ (N x)| ∂μ) := integral_const_mul _ _
    _ = C*(∫ n, |poissonLikelihoodSecond rate θ n| ∂poissonMeasure rate) := congrArg (fun t => C*t) hIntegral
    _ ≤ C*(4*(rate : ℝ)) := mul_le_mul_of_nonneg_left (poissonLikelihoodSecond_L1_uniform rate hHalf) hC
    _ = _ := by ring

end ProphetSecretary.Probability
