import ProphetSecretary.Model.Simulation
import ProphetSecretary.Model.ScalarObjectiveBounds

/-!
# Restricting finite instances and ignoring additional offers

Coordinate projection sends the independent instance law to the restricted product law.
A policy on those identities can be used in the larger instance by ignoring every other
arrival. This derives monotonicity of the optimal scalar value under adding options.
-/

open MeasureTheory Set ProbabilityTheory

namespace ProphetSecretary.Model

variable {n m : ℕ}

lemma measurePreserving_restrictCoordinates (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (e : Fin m ↪ Fin n) :
    MeasurePreserving (fun x : Fin n → ℝ => x ∘ e) (Measure.pi μ) (Measure.pi (fun i => μ (e i))) := by
  have hi := iIndepFun.precomp e.injective
    (iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id))
  have hm := iIndepFun.map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable) hi
  have he : (fun i => (Measure.pi μ).map (fun x => x (e i))) = fun i => μ (e i) := by
    funext i
    exact (measurePreserving_eval μ (e i)).map_eq
  change (Measure.pi μ).map (fun x => x ∘ e) =
    Measure.pi (fun i => (Measure.pi μ).map (fun x => x (e i))) at hm
  rw [he] at hm
  exact ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply (e i)), hm⟩

namespace Instance

/-- Restriction preserves independent marginal laws under an injective relabeling. -/
def restrictBy (P : Instance n) (e : Fin m ↪ Fin n) : Instance m where
  law i := P.law (e i)
  probability i := P.probability (e i)
  nonnegative i := P.nonnegative (e i)

lemma restrictValues_measurePreserving (P : Instance n) (e : Fin m ↪ Fin n) :
    MeasurePreserving (fun x : Fin n → ℝ => x ∘ e) P.valuesLaw (P.restrictBy e).valuesLaw :=
  measurePreserving_restrictCoordinates P.law e

lemma restrictClocks_measurePreserving (e : Fin m ↪ Fin n) :
    MeasurePreserving (fun u : Fin n → ℝ => u ∘ e) (clocksLaw n) (clocksLaw m) :=
  measurePreserving_restrictCoordinates (fun _ => uniformClock) e

lemma maximum_restrict_le (e : Fin m ↪ Fin n) (x : Fin n → ℝ) :
    maximum (x ∘ e) ≤ maximum x :=
  maximum_le _ (maximum_nonnegative x) (fun i => le_maximum x (e i))

lemma restrictBy_integrable_maximum (P : Instance n) (e : Fin m ↪ Fin n)
    (hP : Integrable maximum P.valuesLaw) : Integrable maximum (P.restrictBy e).valuesLaw := by
  apply (P.restrictBy e).integrable_maximum
  intro i
  exact (P.integrable_maximum_iff.mp hP) (e i)

lemma restrictBy_expectedMaximum_le (P : Instance n) (e : Fin m ↪ Fin n)
    (hP : Integrable maximum P.valuesLaw) : (P.restrictBy e).expectedMaximum ≤ P.expectedMaximum := by
  have hp := P.restrictValues_measurePreserving e
  have heq := integral_map (μ := P.valuesLaw) hp.measurable.aemeasurable measurable_maximum.aestronglyMeasurable
  rw [hp.map_eq] at heq
  rw [expectedMaximum, heq]
  exact integral_mono_ae (hp.integrable_comp_of_integrable (P.restrictBy_integrable_maximum e hP)) hP
    (Filter.Eventually.of_forall fun x => maximum_restrict_le e x)

variable {Seed : Type*} [MeasurableSpace Seed]

def projectWorld (e : Fin m ↪ Fin n) (ω : World n Seed) : World m Seed :=
  (ω.1 ∘ e, (ω.2.1 ∘ e, ω.2.2))

lemma projectWorld_measurePreserving (P : Instance n) (e : Fin m ↪ Fin n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (projectWorld e) (P.worldLaw ν) ((P.restrictBy e).worldLaw ν) :=
  (P.restrictValues_measurePreserving e).prod
    ((restrictClocks_measurePreserving e).prod (MeasurePreserving.id ν))

end Instance

namespace RandomizedPolicy

/-- An arbitrary randomized policy on restricted identities remains an online policy
when additional offers are revealed: it ignores those observations. -/
noncomputable def ignoreExtras (π : RandomizedPolicy m) (e : Fin m ↪ Fin n) : RandomizedPolicy n where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := π.rule.ignoreExtras e
  measurable_rule := π.rule.ignoreExtras_isMeasurable π.measurable_rule e

lemma ignoreExtras_expectedReward (π : RandomizedPolicy m) (P : Instance n) (e : Fin m ↪ Fin n) :
    (π.ignoreExtras e).expectedReward P = π.expectedReward (P.restrictBy e) := by
  have hp := P.projectWorld_measurePreserving e π.seedLaw
  have heq := integral_map (μ := P.worldLaw π.seedLaw) hp.measurable.aemeasurable
    π.measurable_realizedReward.aestronglyMeasurable
  rw [hp.map_eq] at heq
  change ∫ ω, (π.ignoreExtras e).realizedReward ω ∂P.worldLaw π.seedLaw = _
  calc
    _ = ∫ ω, π.realizedReward (Instance.projectWorld e ω) ∂P.worldLaw π.seedLaw := by
      apply integral_congr_ae
      filter_upwards [P.world_clocks_distinct π.seedLaw] with ω hω
      exact π.rule.ignoreExtras_reward e ω.2.2 ω.1 ω.2.1 (hω.comp e.injective)
    _ = π.expectedReward (P.restrictBy e) := heq.symm

lemma ignoreExtras_expectedDuration (π : RandomizedPolicy m) (P : Instance n) (e : Fin m ↪ Fin n) :
    (π.ignoreExtras e).expectedDuration P = π.expectedDuration (P.restrictBy e) := by
  have hp := P.projectWorld_measurePreserving e π.seedLaw
  have heq := integral_map (μ := P.worldLaw π.seedLaw) hp.measurable.aemeasurable
    π.measurable_realizedDuration.aestronglyMeasurable
  rw [hp.map_eq] at heq
  change ∫ ω, (π.ignoreExtras e).realizedDuration ω ∂P.worldLaw π.seedLaw = _
  calc
    _ = ∫ ω, π.realizedDuration (Instance.projectWorld e ω) ∂P.worldLaw π.seedLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => π.rule.ignoreExtras_stoppingTime e ω.2.2 ω.1 ω.2.1
    _ = π.expectedDuration (P.restrictBy e) := heq.symm

lemma ignoreExtras_scalarObjective (π : RandomizedPolicy m) (P : Instance n)
    (e : Fin m ↪ Fin n) (hP : Integrable Instance.maximum P.valuesLaw) (w c : ℝ) :
    (π.ignoreExtras e).scalarObjective P w c = π.scalarObjective (P.restrictBy e) w c := by
  rw [(π.ignoreExtras e).scalarObjective_eq P hP,
    π.scalarObjective_eq (P.restrictBy e) (P.restrictBy_integrable_maximum e hP),
    ignoreExtras_expectedReward, ignoreExtras_expectedDuration]

end RandomizedPolicy

lemma optimalScalarValue_restrictBy_le (P : Instance n) (e : Fin m ↪ Fin n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue (P.restrictBy e) w c ≤ optimalScalarValue P w c := by
  apply csSup_le (scalarValues_nonempty (P.restrictBy e) w c)
  rintro v ⟨π, rfl⟩
  rw [← π.ignoreExtras_scalarObjective P e hP]
  exact scalarObjective_le_optimal (π.ignoreExtras e) P hP hw hc

end ProphetSecretary.Model
