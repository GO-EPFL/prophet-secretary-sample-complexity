import ProphetSecretary.Limiting.CountableIndividualLikelihood

/-!
# Fixed-policy individual likelihood responses

The policy callbacks and their independent seed law remain fixed. The scalar
response and duration response are differentiated separately from any change
of optimizer.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Limiting
open CountableInstance

theorem RandomizedCountablePolicy.hasDerivAt_scalarObjective_individualLikelihoodPolicy
    {B : CountableInstance} (π : RandomizedCountablePolicy B) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) (w c : ℝ) :
    HasDerivAt (fun θ => (π.individualLikelihoodPolicy i h hh hb hm θ).scalarObjective w c)
      (π.scalarIndividualLikelihoodDerivative i w c h) 0 := by
  have hAffine : HasDerivAt
      (fun θ : ℝ => π.scalarObjective w c+θ*π.scalarIndividualLikelihoodDerivative i w c h)
      (π.scalarIndividualLikelihoodDerivative i w c h) 0 :=
    (hasDerivAt_mul_const (x := 0) _).const_add _
  apply hAffine.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (by norm_num : -(1/4 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1/4)] with θ hθ
  exact π.individualLikelihoodPolicy_scalarObjective i h hh hb hm (abs_le.mpr hθ) w c

theorem RandomizedCountablePolicy.hasDerivAt_expectedDuration_individualLikelihoodPolicy
    {B : CountableInstance} (π : RandomizedCountablePolicy B) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) :
    HasDerivAt (fun θ => (π.individualLikelihoodPolicy i h hh hb hm θ).expectedDuration)
      (∫ v, π.rule.realizedDuration v*h (v.2.1 i) ∂B.completeWorldLaw π.seedLaw) 0 := by
  have hAffine : HasDerivAt (fun θ : ℝ => π.expectedDuration+
      θ*(∫ v, π.rule.realizedDuration v*h (v.2.1 i) ∂B.completeWorldLaw π.seedLaw))
      (∫ v, π.rule.realizedDuration v*h (v.2.1 i) ∂B.completeWorldLaw π.seedLaw) 0 :=
    (hasDerivAt_mul_const (x := 0) _).const_add _
  apply hAffine.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (by norm_num : -(1/4 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1/4)] with θ hθ
  exact π.individualLikelihoodPolicy_expectedDuration i h hh hb hm (abs_le.mpr hθ)

end ProphetSecretary.Limiting
