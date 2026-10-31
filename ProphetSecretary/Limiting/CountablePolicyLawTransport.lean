import ProphetSecretary.Limiting.CountableScalarObjectives

/-!
# Full policy transport under equivalent observation laws

Absolute continuity transfers almost-sure first attainment for the same
observable callbacks. Mutual absolute continuity identifies the unrestricted
policy suprema on one common policy index set; it does not replace general
competing policies by Markov rules.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

noncomputable def RandomizedCountablePolicy.scalarPayoff {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (w c : ℝ) (v : CompleteWorld π.Seed) : ℝ :=
  w*π.rule.realizedReward B.terminal v+c*π.rule.realizedDuration v

lemma RandomizedCountablePolicy.measurable_scalarPayoff {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (w c : ℝ) : Measurable (π.scalarPayoff w c) :=
  ((π.rule.measurable_realizedReward π.measurable_rule B.terminal).const_mul w).add
    ((π.rule.measurable_realizedDuration π.measurable_rule).const_mul c)

lemma RandomizedCountablePolicy.integrable_scalarPayoff {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (w c : ℝ) :
    Integrable (π.scalarPayoff w c) (B.completeWorldLaw π.seedLaw) :=
  (π.integrable_reward.const_mul w).add (π.integrable_duration.const_mul c)

lemma RandomizedCountablePolicy.scalarObjective_eq_integral {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (w c : ℝ) :
    π.scalarObjective w c=∫ v, π.scalarPayoff w c v ∂B.completeWorldLaw π.seedLaw := by
  rw [show π.scalarPayoff w c=(fun v => w*π.rule.realizedReward B.terminal v+c*π.rule.realizedDuration v) from rfl,
    integral_add (π.integrable_reward.const_mul w) (π.integrable_duration.const_mul c),
    integral_const_mul,integral_const_mul]
  rfl

lemma RandomizedCountablePolicy.scalarPayoff_bounded {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    ∀ᵐ v ∂B.completeWorldLaw π.seedLaw, π.scalarPayoff w c v ∈ Icc (0 : ℝ) (w*(B.cap : ℝ)+c) := by
  filter_upwards [π.rule.reward_bounded B π.seedLaw] with v hv
  have ht := π.rule.duration_bounds v
  constructor
  · exact add_nonneg (mul_nonneg hw hv.1) (mul_nonneg hc ht.1)
  · have h := add_le_add (mul_le_mul_of_nonneg_left hv.2 hw) (mul_le_mul_of_nonneg_left ht.2 hc)
    simpa only [scalarPayoff,mul_one] using h

noncomputable def RandomizedCountablePolicy.changeInstance {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (D : CountableInstance)
    (hAC : D.completeWorldLaw π.seedLaw ≪ B.completeWorldLaw π.seedLaw) : RandomizedCountablePolicy D where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := π.rule
  measurable_rule := π.measurable_rule
  admissible := hAC.ae_le π.admissible

lemma RandomizedCountablePolicy.changeInstance_scalarPayoff {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (D : CountableInstance)
    (hAC : D.completeWorldLaw π.seedLaw ≪ B.completeWorldLaw π.seedLaw)
    (hTerm : D.terminal=B.terminal) (w c : ℝ) (v : CompleteWorld π.Seed) :
    (π.changeInstance D hAC).scalarPayoff w c v=π.scalarPayoff w c v := by
  simp only [scalarPayoff,changeInstance,hTerm]

lemma CountableInstance.optimalScalarValue_eq_sSup_transport (B D : CountableInstance)
    (hBD : ∀ π : RandomizedCountablePolicy B, D.completeWorldLaw π.seedLaw ≪ B.completeWorldLaw π.seedLaw)
    (hDB : ∀ π : RandomizedCountablePolicy D, B.completeWorldLaw π.seedLaw ≪ D.completeWorldLaw π.seedLaw)
    (w c : ℝ) :
    D.optimalScalarValue w c=sSup (Set.range (fun π : RandomizedCountablePolicy B =>
      (π.changeInstance D (hBD π)).scalarObjective w c)) := by
  unfold CountableInstance.optimalScalarValue CountableInstance.scalarPayoffs
  congr 1
  ext z
  constructor
  · rintro ⟨π,rfl⟩
    exact ⟨π.changeInstance B (hDB π),rfl⟩
  · rintro ⟨π,rfl⟩
    exact ⟨π.changeInstance D (hBD π),rfl⟩

end ProphetSecretary.Limiting
