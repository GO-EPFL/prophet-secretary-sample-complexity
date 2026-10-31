import ProphetSecretary.Limiting.FinitePotentialBranch
import ProphetSecretary.Limiting.HybridScalarMixture

/-!
# Integrable finite-design residual on the actual hybrid law

The analytical finite-array sum uses the same fixed hybrid rule on every count.
A count factor is needed only for integrability; the initial continuation value
and each retained-state potential ignore appended zero identities.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*}

lemma totalFirstMoment_appendZeros (Q : Model.Instance n) (N : ℕ) :
    (Q.appendZeros N).totalFirstMoment = Q.totalFirstMoment := by
  simp [Model.Instance.totalFirstMoment, Model.Instance.appendZeros, Fin.sum_univ_add]

lemma totalFirstMoment_appendIID (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (N : ℕ) :
    (appendIID P κ hκ N).totalFirstMoment = P.totalFirstMoment + (N : ℝ) * ∫ x, x ∂κ := by
  simp [Model.Instance.totalFirstMoment, appendIID, Fin.sum_univ_add]

noncomputable def HybridRule.designResidual (π : HybridRule n Seed) (Q P : Model.Instance n)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (w c : ℝ) (v : HybridWorld n Seed) : ℝ :=
  (π.asFinitePolicy v.1.1).reachedTransitionResidual (Q.appendZeros v.1.1) (appendIID P κ hκ v.1.1) w c
    v.2.2.2 (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2)

variable [MeasurableSpace Seed]

lemma HybridRule.measurable_designResidual (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (Q P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Measurable (π.designResidual Q P κ hκ w c) := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × Model.World n Seed
  have hr : Measurable (fun v : Ω => v.2.2.2) := by fun_prop
  have hx (i : Fin n) : Measurable (fun v : Ω => v.2.1 i) := by fun_prop
  have hu (i : Fin n) : Measurable (fun v : Ω => v.2.2.1 i) := by fun_prop
  have hv (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  have hI' : Integrable (fun x : ℝ => x) κ := by convert! hI using 1
  exact (π.asFinitePolicy N).measurable_reachedTransitionResidual (π.asFinitePolicy_isMeasurable hπ N)
    (Q.appendZeros N) (appendIID P κ hκ N) (Q.appendZeros_integrable_maximum N hQ)
      (appendIID_integrable_maximum P κ hκ N hP hI') hw hc hr
        (fun j => measurable_combinedValues_family (fun v : Ω => v.2.1) hx (fun v : Ω => v.1) hv j)
        (fun j => measurable_combinedClocks_family (fun v : Ω => v.2.2.1) hu (fun v : Ω => v.1) hv j)

omit [MeasurableSpace Seed] in
lemma HybridRule.abs_designResidual_le (π : HybridRule n Seed) (Q P : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (hP : Integrable Model.Instance.maximum P.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (v : HybridWorld n Seed) :
    |π.designResidual Q P κ hκ w c v| ≤
      w * (Q.totalFirstMoment + P.totalFirstMoment + (v.1.1 : ℝ) * ∫ x, x ∂κ) := by
  have hI' : Integrable (fun x : ℝ => x) κ := by convert! hI using 1
  have h := (π.asFinitePolicy v.1.1).abs_reachedTransitionResidual_le (Q.appendZeros v.1.1)
    (appendIID P κ hκ v.1.1) (Q.appendZeros_integrable_maximum v.1.1 hQ)
      (appendIID_integrable_maximum P κ hκ v.1.1 hP hI') hw hc v.2.2.2
        (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2)
  rw [totalFirstMoment_appendZeros, totalFirstMoment_appendIID] at h
  simpa only [HybridRule.designResidual, add_assoc] using h

lemma HybridRule.integrable_designResidual (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (Q P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (π.designResidual Q P κ hκ w c) (hybridWorldLaw P μ ν) := by
  have hcount : Integrable (fun v : HybridWorld n Seed => (v.1.1 : ℝ)) (hybridWorldLaw P μ ν) :=
    (measurePreserving_fst (μ := configurationLaw μ) (ν := P.worldLaw ν)).integrable_comp_of_integrable
      (configuration_count_integrable μ)
  have hi : Integrable (fun v : HybridWorld n Seed =>
      w * (Q.totalFirstMoment + P.totalFirstMoment + (v.1.1 : ℝ) * ∫ x, x ∂κ)) (hybridWorldLaw P μ ν) :=
    ((integrable_const _).add (hcount.mul_const _)).const_mul w
  apply hi.mono' (π.measurable_designResidual hπ Q P hQ hP κ hκ hI hw hc).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun v => by
    rw [Real.norm_eq_abs]
    exact π.abs_designResidual_le Q P hQ hP κ hκ hI hw.le hc v)

lemma RandomizedHybridPolicy.designResidual_branchIntegral (π : RandomizedHybridPolicy n)
    (Q P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ) (N : ℕ) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ v, π.rule.designResidual Q P κ hκ w c (configurationMk N v.1, v.2)
      ∂(Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod κ)).prod (P.worldLaw π.seedLaw)) =
      (π.finiteEvaluation N).expectedReachedTransitionResidual (Q.appendZeros N) (appendIID P κ hκ N) w c := by
  have hI' : Integrable (fun x : ℝ => x) κ := by convert! hI using 1
  have hm : Measurable (fun ω : (π.finiteEvaluation N).World =>
      (π.finiteEvaluation N).rule.reachedTransitionResidual (Q.appendZeros N) (appendIID P κ hκ N) w c ω.2.2 ω.1 ω.2.1) :=
    (π.finiteEvaluation N).rule.measurable_reachedTransitionResidual (π.finiteEvaluation N).measurable_rule
      (Q.appendZeros N) (appendIID P κ hκ N) (Q.appendZeros_integrable_maximum N hQ)
      (appendIID_integrable_maximum P κ hκ N hP hI') hw hc (by fun_prop) (fun _ => by fun_prop) (fun _ => by fun_prop)
  have hmp := finiteArrayWorld_measurePreserving P κ hκ π.seedLaw N
  have h := integral_map (μ := (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod κ)).prod
    (P.worldLaw π.seedLaw)) hmp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hmp.map_eq] at h
  exact h.symm

end ProphetSecretary.Limiting
