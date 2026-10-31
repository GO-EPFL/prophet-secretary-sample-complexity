import ProphetSecretary.Model.ExtendedExpectations
import Mathlib.Probability.Distributions.Uniform

/-!
# A uniformly random identity

Choose one identity uniformly using the independent seed, then wait for that identity.
The rule is legal on every history and does not inspect unseen values. Its extended
expected reward is the average of all marginal extended means, so the same rule obtains
infinite expected reward whenever the expected maximum is infinite.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable abbrev RandomizedPolicy.uniformIdentity (hn : 0 < n) : RandomizedPolicy n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact {
    Seed := Fin n
    seedLaw := (PMF.uniformOfFintype (Fin n)).toMeasure
    rule := ⟨fun r t j v h => (chooseIdentity r).rule.decide () t j v h⟩
    measurable_rule := by
      let T := Fin n × (ℝ × (Fin n × (ℝ × History n)))
      have hr : Measurable (fun z : T => z.1) := measurable_fst
      have hj : Measurable (fun z : T => z.2.2.1) :=
        measurable_fst.comp (measurable_snd.comp measurable_snd)
      exact (measurable_of_finite (fun p : Fin n × Fin n => decide (p.2 = p.1))).comp
        (hr.prodMk hj) }

/-- Uniformity is an equality of actual singleton probabilities. -/
lemma RandomizedPolicy.uniformIdentity_seedLaw_singleton (hn : 0 < n) (i : Fin n) :
    (uniformIdentity hn).seedLaw {i} = (n : ℝ≥0∞)⁻¹ := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  change (PMF.uniformOfFintype (Fin n)).toMeasure {i} = (n : ℝ≥0∞)⁻¹
  rw [PMF.toMeasure_apply_singleton _ i (measurableSet_singleton i)]
  simp

/-- The selected identity has the uniform marginal even on the complete execution space. -/
lemma RandomizedPolicy.uniformIdentity_identityLaw (P : Instance n) (hn : 0 < n) :
    Measure.map (fun ω : (uniformIdentity hn).World => ω.2.2)
      (P.worldLaw (uniformIdentity hn).seedLaw) = (uniformIdentity hn).seedLaw := by
  exact (measurePreserving_snd.comp measurePreserving_snd).map_eq

/-- The identity seed is independent of the entire offer vector. -/
lemma RandomizedPolicy.uniformIdentity_independent_values (P : Instance n) (hn : 0 < n) :
    IndepFun (fun ω : (uniformIdentity hn).World => ω.1)
      (fun ω => ω.2.2) (P.worldLaw (uniformIdentity hn).seedLaw) := by
  exact indepFun_prod measurable_id measurable_snd

/-- The seed is independent of offers and clocks jointly. -/
lemma RandomizedPolicy.uniformIdentity_independent_environment (P : Instance n) (hn : 0 < n) :
    IndepFun (fun ω : (uniformIdentity hn).World => (ω.1, ω.2.1))
      (fun ω => ω.2.2) (P.worldLaw (uniformIdentity hn).seedLaw) := by
  let π := uniformIdentity hn
  have ha := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc P.valuesLaw (Instance.clocksLaw n) π.seedLaw)
  have hv := measurePreserving_fst.comp ha
  have hr := measurePreserving_snd.comp ha
  change MeasurePreserving (fun ω : π.World => (ω.1, ω.2.1))
    (P.worldLaw π.seedLaw) (P.valuesLaw.prod (Instance.clocksLaw n)) at hv
  change MeasurePreserving (fun ω : π.World => ω.2.2)
    (P.worldLaw π.seedLaw) π.seedLaw at hr
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).mpr
  change Measure.map (fun ω : π.World => ((ω.1, ω.2.1), ω.2.2)) (P.worldLaw π.seedLaw) =
    (Measure.map (fun ω : π.World => (ω.1, ω.2.1)) (P.worldLaw π.seedLaw)).prod
      (Measure.map (fun ω : π.World => ω.2.2) (P.worldLaw π.seedLaw))
  rw [hv.map_eq, hr.map_eq]
  exact ha.map_eq

/-- Every callback, including unreachable histories, waits only for the sampled identity. -/
lemma RandomizedPolicy.uniformIdentity_decide (hn : 0 < n) (r j : Fin n)
    (t v : ℝ) (h : History n) :
    (uniformIdentity hn).rule.decide r t j v h = decide (j = r) := rfl

lemma RandomizedPolicy.uniformIdentity_reward (hn : 0 < n) (r : Fin n)
    (x u : Fin n → ℝ) (hur : u r ≤ 1) :
    (uniformIdentity hn).rule.reward r Finset.univ x u = x r := by
  change (chooseIdentity r).rule.reward () Finset.univ x u = x r
  exact chooseIdentity_reward r () x u hur

lemma RandomizedPolicy.uniformIdentity_lintegral (hn : 0 < n) (f : Fin n → ℝ≥0∞) :
    ∫⁻ i, f i ∂(uniformIdentity hn).seedLaw = (n : ℝ≥0∞)⁻¹ * ∑ i, f i := by
  change (∫⁻ i : Fin n, f i ∂((uniformIdentity hn).seedLaw : Measure (Fin n))) = _
  rw [lintegral_countable', tsum_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [uniformIdentity_seedLaw_singleton]
    exact mul_comm _ _

lemma RandomizedPolicy.uniformIdentity_extendedExpectedReward (P : Instance n)
    (hn : 0 < n) :
    (uniformIdentity hn).extendedExpectedReward P =
      (n : ℝ≥0∞)⁻¹ * ∑ i, P.extendedCoordinateMean i := by
  let π := uniformIdentity hn
  have heq : (fun ω : π.World => ENNReal.ofReal (π.realizedReward ω)) =ᵐ[
      P.worldLaw π.seedLaw] (fun ω => ENNReal.ofReal (ω.1 ω.2.2)) := by
    filter_upwards [P.world_clocks_mem_unitInterval π.seedLaw] with ω hω
    exact congrArg ENNReal.ofReal (uniformIdentity_reward hn ω.2.2 ω.1 ω.2.1
      (hω ω.2.2).2)
  have hm : AEMeasurable (fun ω : π.World => ENNReal.ofReal (ω.1 ω.2.2))
      (P.worldLaw π.seedLaw) :=
    π.measurable_realizedReward.ennreal_ofReal.aemeasurable.congr heq
  calc
    _ = ∫⁻ ω : π.World, ENNReal.ofReal (ω.1 ω.2.2) ∂P.worldLaw π.seedLaw :=
      lintegral_congr_ae heq
    _ = ∫⁻ x, ∫⁻ ur, ENNReal.ofReal (x ur.2)
        ∂(Instance.clocksLaw n).prod π.seedLaw ∂P.valuesLaw :=
      lintegral_prod _ hm
    _ = ∫⁻ x, (n : ℝ≥0∞)⁻¹ * ∑ i, ENNReal.ofReal (x i) ∂P.valuesLaw := by
      apply lintegral_congr
      intro x
      have hx : Measurable (fun ur : (Fin n → ℝ) × Fin n => ENNReal.ofReal (x ur.2)) :=
        (measurable_of_finite (fun i : Fin n => ENNReal.ofReal (x i))).comp measurable_snd
      rw [lintegral_prod_symm _ hx.aemeasurable]
      simp only [lintegral_const, measure_univ, mul_one]
      exact uniformIdentity_lintegral hn _
    _ = (n : ℝ≥0∞)⁻¹ * ∑ i, P.extendedCoordinateMean i := by
      rw [lintegral_const_mul _ (by fun_prop), lintegral_finsetSum _ (by fun_prop)]
      simp_rw [← P.extendedCoordinateMean_eq]

/-- In the finite-mean setting the same policy has the usual average first moment. -/
lemma RandomizedPolicy.uniformIdentity_expectedReward (P : Instance n) (hn : 0 < n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    (uniformIdentity hn).expectedReward P =
      (n : ℝ)⁻¹ * ∑ i, ∫ x, x ∂P.law i := by
  have hm : ∀ i : Fin n, 0 ≤ ∫ x, x ∂P.law i :=
    fun i => integral_nonneg_of_ae (P.nonnegative i)
  have he : ∀ i : Fin n, P.extendedCoordinateMean i = ENNReal.ofReal (∫ x, x ∂P.law i) :=
    fun i => (ofReal_integral_eq_lintegral_ofReal
      (P.integrable_maximum_iff.mp hP i) (P.nonnegative i)).symm
  have h := uniformIdentity_extendedExpectedReward P hn
  rw [extendedExpectedReward_eq_of_integrable _ P hP] at h
  simp_rw [he] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hm i)] at h
  have ht := congrArg ENNReal.toReal h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (uniformIdentity hn |>.expectedReward_nonnegative P),
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => hm i))] using ht

/-- One distribution-independent uniform identity policy suffices for every infinite-mean
instance of the given nonzero size. -/
theorem RandomizedPolicy.uniformIdentity_extendedExpectedReward_eq_top (P : Instance n)
    (hn : 0 < n) (hP : P.extendedExpectedMaximum = ⊤) :
    (uniformIdentity hn).extendedExpectedReward P = ⊤ := by
  have hsum : ∑ i, P.extendedCoordinateMean i = ⊤ := by
    apply top_le_iff.mp
    rw [← hP]
    exact P.extendedExpectedMaximum_le_sum
  rw [uniformIdentity_extendedExpectedReward, hsum]
  exact ENNReal.mul_top (by simp)

end ProphetSecretary.Model
