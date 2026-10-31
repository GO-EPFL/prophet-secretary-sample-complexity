import ProphetSecretary.Model.Outcome
import ProphetSecretary.Reach.Pending

/-!
# Scalar objectives and their optimization

The supremum is taken over measurable history-dependent policies with arbitrary independent
auxiliary probability spaces. In particular it is not a supremum over Markov thresholds.
The finite expected maximum is an explicit premise of the integrability and optimization
lemmas. Bounded zero-mean auxiliary instances are permitted.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

/-- A general admissible randomized online policy, including its independent random seed. -/
structure RandomizedPolicy (n : ℕ) where
  Seed : Type
  [seedSpace : MeasurableSpace Seed]
  seedLaw : Measure Seed
  [probability : IsProbabilityMeasure seedLaw]
  rule : Policy Seed n
  measurable_rule : rule.IsMeasurable

attribute [instance] RandomizedPolicy.seedSpace RandomizedPolicy.probability

namespace RandomizedPolicy

variable {n : ℕ} (π : RandomizedPolicy n)

abbrev World := (Fin n → ℝ) × ((Fin n → ℝ) × π.Seed)

noncomputable def realizedReward (ω : π.World) : ℝ :=
  π.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1

noncomputable def realizedDuration (ω : π.World) : ℝ :=
  π.rule.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1

lemma measurable_realizedReward : Measurable π.realizedReward := by
  exact π.rule.measurable_reward π.measurable_rule
    (measurable_snd.comp measurable_snd)
    (fun i => (measurable_pi_apply i).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) Finset.univ

lemma measurable_realizedDuration : Measurable π.realizedDuration := by
  exact π.rule.measurable_stoppingTime π.measurable_rule
    (measurable_snd.comp measurable_snd)
    (fun i => (measurable_pi_apply i).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) Finset.univ

lemma integrable_realizedReward (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    Integrable π.realizedReward (P.worldLaw π.seedLaw) := by
  have hv : MeasurePreserving (fun ω : π.World => ω.1) (P.worldLaw π.seedLaw) P.valuesLaw :=
    measurePreserving_fst
  have hm := hv.integrable_comp_of_integrable hP
  apply hm.mono' π.measurable_realizedReward.aestronglyMeasurable
  filter_upwards [hv.quasiMeasurePreserving.ae P.ae_nonnegative] with ω hω
  change ‖π.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1‖ ≤ Instance.maximum ω.1
  rw [Real.norm_eq_abs, abs_of_nonneg (π.rule.reward_nonnegative _ _ _ _ hω)]
  exact π.rule.reward_le_maximum _ _ _ _

lemma integrable_realizedDuration (P : Instance n) :
    Integrable π.realizedDuration (P.worldLaw π.seedLaw) := by
  exact P.integrable_worldTime π.seedLaw π.rule π.measurable_rule Finset.univ

/-- Expected selected reward; it includes the policy's independent randomness. -/
noncomputable def expectedReward (P : Instance n) : ℝ :=
  ∫ ω, π.realizedReward ω ∂P.worldLaw π.seedLaw

/-- Expected stopping time, with duration one on no selection. -/
noncomputable def expectedDuration (P : Instance n) : ℝ :=
  ∫ ω, π.realizedDuration ω ∂P.worldLaw π.seedLaw

/-- `J_P(π;w,c)` from the manuscript. -/
noncomputable def scalarObjective (P : Instance n) (w c : ℝ) : ℝ :=
  ∫ ω, (w * π.realizedReward ω + c * π.realizedDuration ω) ∂P.worldLaw π.seedLaw

lemma scalarObjective_eq (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (w c : ℝ) : π.scalarObjective P w c = w * π.expectedReward P + c * π.expectedDuration P := by
  rw [scalarObjective, integral_add ((π.integrable_realizedReward P hP).const_mul w)
    ((π.integrable_realizedDuration P).const_mul c), integral_const_mul, integral_const_mul]
  rfl

lemma expectedReward_nonnegative (P : Instance n) : 0 ≤ π.expectedReward P := by
  apply integral_nonneg_of_ae
  have hv : MeasurePreserving (fun ω : π.World => ω.1) (P.worldLaw π.seedLaw) P.valuesLaw :=
    measurePreserving_fst
  filter_upwards [hv.quasiMeasurePreserving.ae P.ae_nonnegative] with ω hω
  exact π.rule.reward_nonnegative _ _ _ _ hω

lemma expectedReward_le_maximum (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    π.expectedReward P ≤ P.expectedMaximum := by
  have hv : MeasurePreserving (fun ω : π.World => ω.1) (P.worldLaw π.seedLaw) P.valuesLaw :=
    measurePreserving_fst
  have h := integral_mono (π.integrable_realizedReward P hP)
    (hv.integrable_comp_of_integrable hP) (fun ω => π.rule.reward_le_maximum _ _ _ _)
  have heq := integral_map (μ := P.worldLaw π.seedLaw) hv.measurable.aemeasurable Instance.measurable_maximum.aestronglyMeasurable
  rw [hv.map_eq] at heq
  exact h.trans_eq heq.symm

end RandomizedPolicy

/-- The individual instance's optimal scalar value `V(P;w,c)`. -/
noncomputable def optimalScalarValue {n : ℕ} (P : Instance n) (w c : ℝ) : ℝ :=
  sSup {v | ∃ π : RandomizedPolicy n, v = π.scalarObjective P w c}

/-- The optimal global reward ratio. The infimum includes every finite instance size. -/
noncomputable def optimalCompetitiveRatio : ℝ :=
  sInf {r | ∃ (n : ℕ) (P : Instance n), P.HasPositiveFiniteMaximum ∧
    r = optimalScalarValue P 1 0 / P.expectedMaximum}

/-- The scalar gap `𝓕(P;w,c)` at the global constant, distinct from regret at a fixed instance. -/
noncomputable def scalarGap {n : ℕ} (P : Instance n) (w c : ℝ) : ℝ :=
  optimalScalarValue P w c - optimalCompetitiveRatio * (w * P.expectedMaximum + c)

/-- The normalized gap `F_P(λ)` with reward/duration weights `(λ,1−λ)`. -/
noncomputable def normalizedScalarGap {n : ℕ} (P : Instance n) (lam : ℝ) : ℝ :=
  scalarGap P lam (1 - lam)

end ProphetSecretary.Model
