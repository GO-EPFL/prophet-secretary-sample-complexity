import ProphetSecretary.Probability.MappedReachResidual

/-!
# Performance identities for transformed payoffs

The observer retains the original values and zero identities. Only the selected
reward is transformed. A general design law supplies the continuation potential;
the identity includes its residual against the actual mapped reward law.
Paper correspondence: `upmom:transport` and value-perturbation envelopes.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def RandomizedPolicy.mappedRewardDifference (π : RandomizedPolicy n)
    (f : Fin n → ℝ → ℝ) (ω : π.World) : ℝ :=
  π.rule.mappedReward f ω.2.2 Finset.univ ω.1 ω.2.1 - π.realizedReward ω

noncomputable def RandomizedPolicy.mappedScalarObjective (π : RandomizedPolicy n)
    (P : Instance n) (f : Fin n → ℝ → ℝ) (w c : ℝ) : ℝ :=
  ∫ ω : π.World, w * π.rule.mappedReward f ω.2.2 Finset.univ ω.1 ω.2.1 +
    c * π.realizedDuration ω ∂P.worldLaw π.seedLaw

lemma RandomizedPolicy.integrable_mappedRewardDifference (π : RandomizedPolicy n)
    (P : Instance n) (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    {h : ℝ} (hh : 0 ≤ h) (hdispl : ∀ i a, |f i a - a| ≤ h) :
    Integrable (π.mappedRewardDifference f) (P.worldLaw π.seedLaw) := by
  have hm := π.rule.measurable_mappedReward π.measurable_rule f hf
    (measurable_snd.comp measurable_snd) (fun i => (measurable_pi_apply i).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) Finset.univ
  apply Integrable.of_bound (hm.sub π.measurable_realizedReward).aestronglyMeasurable h
  exact Eventually.of_forall fun ω => by
    change ‖π.mappedRewardDifference f ω‖ ≤ h
    rw [Real.norm_eq_abs]
    exact π.rule.mappedReward_abs_difference_le f ω.2.2 Finset.univ ω.1 ω.2.1 hh
      (fun i => hdispl i (ω.1 i))

lemma RandomizedPolicy.mappedScalarObjective_eq (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) {h : ℝ} (hh : 0 ≤ h) (hdispl : ∀ i a, |f i a - a| ≤ h)
    (w c : ℝ) :
    π.mappedScalarObjective P f w c = π.scalarObjective P w c +
      w * (∫ ω, π.mappedRewardDifference f ω ∂P.worldLaw π.seedLaw) := by
  have hJ : Integrable (fun ω => w * π.realizedReward ω + c * π.realizedDuration ω)
      (P.worldLaw π.seedLaw) :=
    ((π.integrable_realizedReward P hP).const_mul w).add ((π.integrable_realizedDuration P).const_mul c)
  have hD := π.integrable_mappedRewardDifference P f hf hh hdispl
  have heq : π.mappedScalarObjective P f w c =
      ∫ ω, (w * π.realizedReward ω + c * π.realizedDuration ω) + w * π.mappedRewardDifference f ω
        ∂P.worldLaw π.seedLaw := by
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by dsimp [mappedRewardDifference]; ring
  rw [heq, integral_add hJ (hD.const_mul w), integral_const_mul]
  rfl

lemma RandomizedPolicy.integrable_reachedResidual_under (π : RandomizedPolicy n)
    (Q T P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hT : Integrable Instance.maximum T.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (fun ω : π.World => π.rule.reachedTransitionResidual Q T w c ω.2.2 ω.1 ω.2.1)
      (P.worldLaw π.seedLaw) := by
  have hm := π.rule.measurable_reachedTransitionResidual π.measurable_rule Q T hQ hT hw hc
    (measurable_snd.comp measurable_snd) (fun i => (measurable_pi_apply i).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  apply Integrable.of_bound hm.aestronglyMeasurable (w * (Q.totalFirstMoment + T.totalFirstMoment))
  exact Eventually.of_forall fun ω => by
    change ‖π.rule.reachedTransitionResidual Q T w c ω.2.2 ω.1 ω.2.1‖ ≤ w * (Q.totalFirstMoment + T.totalFirstMoment)
    simpa only [Real.norm_eq_abs] using π.rule.abs_reachedTransitionResidual_le Q T hQ hT hw.le hc ω.2.2 ω.1 ω.2.1

/-- General-design mapped performance identity. Integrability and residual
cancellation are proved from the product laws and the actual causal execution. -/
theorem RandomizedPolicy.mapped_bellman_performance (π : RandomizedPolicy n)
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h w c : ℝ} (hh : 0 ≤ h) (hw : 0 < w) (hc : 0 ≤ c) (hdispl : ∀ i a, |f i a - a| ≤ h) :
    Integrable (fun ω : π.World => π.rule.mappedReachedLoss Q f w c ω.2.2 ω.1 ω.2.1) (P.worldLaw π.seedLaw) ∧
    optimalScalarValue Q w c - π.mappedScalarObjective P f w c =
      (∫ ω : π.World, π.rule.mappedReachedLoss Q f w c ω.2.2 ω.1 ω.2.1 ∂P.worldLaw π.seedLaw) +
      ∫ ω : π.World, π.rule.reachedTransitionResidual Q (P.mapValues f hf hnn) w c ω.2.2 ω.1 ω.2.1
        ∂P.worldLaw π.seedLaw := by
  let μ := P.worldLaw π.seedLaw
  let S : π.World → ℝ := fun ω => π.rule.reachedBellmanLoss Q w c ω.2.2 ω.1 ω.2.1
  let D : π.World → ℝ := fun ω => π.rule.reachedMaxDifference Q f w c ω.2.2 ω.1 ω.2.1
  let M : π.World → ℝ := fun ω => π.rule.mappedReachedLoss Q f w c ω.2.2 ω.1 ω.2.1
  let R₀ : π.World → ℝ := fun ω => π.rule.reachedTransitionResidual Q P w c ω.2.2 ω.1 ω.2.1
  let R₁ : π.World → ℝ := fun ω => π.rule.reachedTransitionResidual Q (P.mapValues f hf hnn) w c ω.2.2 ω.1 ω.2.1
  have hT := P.mapValues_integrable_of_bounded_displacement hP f hf hnn
    (fun i => Eventually.of_forall (hdispl i))
  have hS : Integrable S μ := π.rule.integrable_reachedBellmanLoss_under π.measurable_rule Q P hQ hP π.seedLaw hw hc
  obtain ⟨hD, hcancel⟩ := π.rule.mappedPremium_residual_cancellation π.measurable_rule Q P hQ hP f hf hnn
    π.seedLaw hh hw hc hdispl
  have hΔ := π.integrable_mappedRewardDifference P f hf hh hdispl
  have hR₀ : Integrable R₀ μ := π.integrable_reachedResidual_under Q P P hQ hP hw hc
  have hR₁ : Integrable R₁ μ := π.integrable_reachedResidual_under Q (P.mapValues f hf hnn) P hQ hT hw hc
  have hpath : ∀ᵐ ω ∂μ, M ω = S ω - D ω - w * π.mappedRewardDifference f ω := by
    filter_upwards [P.world_clocks_distinct π.seedLaw] with ω hω
    have h := π.rule.mappedLoss_difference_identity Q f w c ω.2.2 ω.1 ω.2.1 hω
    dsimp [M, S, D, mappedRewardDifference, realizedReward]
    linarith only [h]
  have hSD : Integrable (fun ω => S ω - D ω) μ := hS.sub hD
  have hM : Integrable M μ := (hSD.sub (hΔ.const_mul w)).congr (hpath.mono fun ω hω => by
    change S ω - D ω - w * π.mappedRewardDifference f ω = M ω
    exact hω.symm)
  have hMI := integral_congr_ae hpath
  rw [integral_sub hSD (hΔ.const_mul w), integral_sub hS hD, integral_const_mul] at hMI
  change (∫ ω, D ω ∂μ) = ∫ ω, R₁ ω - R₀ ω ∂μ at hcancel
  rw [integral_sub hR₁ hR₀] at hcancel
  have hBellman := π.bellman_residualIdentity_split Q P hQ hP hw hc
  change optimalScalarValue Q w c - π.scalarObjective P w c = (∫ ω, R₀ ω ∂μ) + ∫ ω, S ω ∂μ at hBellman
  have hJ := π.mappedScalarObjective_eq P hP f hf hh hdispl w c
  refine ⟨hM, ?_⟩
  change optimalScalarValue Q w c - π.mappedScalarObjective P f w c = (∫ ω, M ω ∂μ) + ∫ ω, R₁ ω ∂μ
  linarith only [hMI, hcancel, hBellman, hJ]

/-- With the actual mapped law as design, the residual vanishes. Original
current-value information cannot improve the scalar optimum of independent
mapped offers. This is proved by the Bellman identity, not assumed as a policy
simulation or conditional-kernel interface. -/
theorem RandomizedPolicy.mapped_bellman_loss_identity (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h w c : ℝ} (hh : 0 ≤ h) (hw : 0 < w) (hc : 0 ≤ c) (hdispl : ∀ i a, |f i a - a| ≤ h) :
    optimalScalarValue (P.mapValues f hf hnn) w c - π.mappedScalarObjective P f w c =
      ∫ ω : π.World, π.rule.mappedReachedLoss (P.mapValues f hf hnn) f w c ω.2.2 ω.1 ω.2.1
        ∂P.worldLaw π.seedLaw := by
  have hQ := P.mapValues_integrable_of_bounded_displacement hP f hf hnn
    (fun i => Eventually.of_forall (hdispl i))
  have h := (π.mapped_bellman_performance (P.mapValues f hf hnn) P hQ hP f hf hnn hh hw hc hdispl).2
  simpa only [Policy.reachedTransitionResidual, Instance.transitionResidual, Instance.lawResidual,
    sub_self, ite_self, Finset.sum_const_zero, integral_zero, add_zero] using h

theorem RandomizedPolicy.mappedScalarObjective_le_optimal (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h w c : ℝ} (hh : 0 ≤ h) (hw : 0 < w) (hc : 0 ≤ c) (hdispl : ∀ i a, |f i a - a| ≤ h) :
    π.mappedScalarObjective P f w c ≤ optimalScalarValue (P.mapValues f hf hnn) w c := by
  have h := π.mapped_bellman_loss_identity P hP f hf hnn hh hw hc hdispl
  have hn : 0 ≤ (∫ ω : π.World,
      π.rule.mappedReachedLoss (P.mapValues f hf hnn) f w c ω.2.2 ω.1 ω.2.1 ∂P.worldLaw π.seedLaw) :=
    integral_nonneg (fun ω =>
      π.rule.mappedReachedLoss_nonnegative (P.mapValues f hf hnn) f w c ω.2.2 ω.1 ω.2.1)
  linarith only [h, hn]

end ProphetSecretary.Model
