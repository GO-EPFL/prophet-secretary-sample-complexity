import ProphetSecretary.Model.ZeroSimulation
import ProphetSecretary.Model.ScalarObjectiveBounds
import ProphetSecretary.Model.ClockReplacement

/-!
# Probability law of zero-offer simulation

Independent zero-offer clocks are moved into the policy's auxiliary seed. The law
transport retains every identity and every zero observation of the augmented execution.
-/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

namespace ProphetSecretary.Model

lemma measurePreserving_finAddCases {n m : ℕ} (μ : Fin n → Measure ℝ)
    (ν : Fin m → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)] :
    MeasurePreserving (fun z : (Fin n → ℝ) × (Fin m → ℝ) => (Fin.addCases z.1 z.2 : Fin (n + m) → ℝ))
      ((Measure.pi μ).prod (Measure.pi ν)) (Measure.pi (Fin.addCases μ ν : Fin (n + m) → Measure ℝ)) := by
  let ρ : Fin (n + m) → Measure ℝ := Fin.addCases μ ν
  haveI : ∀ k, IsProbabilityMeasure (ρ k) := by
    intro k
    induction k using Fin.addCases with
    | left i => simpa [ρ] using (inferInstance : IsProbabilityMeasure (μ i))
    | right j => simpa [ρ] using (inferInstance : IsProbabilityMeasure (ν j))
  let σ : Fin n ⊕ Fin m → Measure ℝ := Sum.elim μ ν
  haveI : ∀ k, IsProbabilityMeasure (σ k) := by intro k; cases k <;> dsimp [σ] <;> infer_instance
  have hsum := measurePreserving_sumPiEquivProdPi_symm σ
  have hfin := measurePreserving_piCongrLeft (α := fun _ : Fin (n + m) => ℝ) ρ finSumFinEquiv
  have he : (fun j : Fin n ⊕ Fin m => ρ (finSumFinEquiv j)) = σ := by
    funext j
    cases j <;> simp [ρ, σ]
  rw [he] at hfin
  have h := hfin.comp hsum
  convert h using 1
  · funext z k
    induction k using Fin.addCases with
    | left i => simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]; rfl
    | right j => simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]; rfl
  · rfl

namespace Instance

variable {n m : ℕ}

/-- Append distinct deterministic-zero distributions. -/
noncomputable def appendZeros (P : Instance n) (m : ℕ) : Instance (n + m) where
  law := Fin.addCases P.law (fun _ => Measure.dirac 0)
  probability := by
    intro k
    induction k using Fin.addCases with
    | left i => simpa using P.probability i
    | right j => simpa using (inferInstance : IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  nonnegative := by
    intro k
    induction k using Fin.addCases with
    | left i => simpa using P.nonnegative i
    | right j => simp

lemma pi_dirac_zero (m : ℕ) :
    Measure.pi (fun _ : Fin m => Measure.dirac (0 : ℝ)) = Measure.dirac (fun _ : Fin m => (0 : ℝ)) := by
  have h := Measure.pi_map_pi (μ := fun _ : Fin m => uniformClock)
    (f := fun _ _ => (0 : ℝ)) (fun _ => measurable_const.aemeasurable)
  simpa only [Measure.map_const, measure_univ, one_smul] using h.symm

lemma appendValues_measurePreserving (P : Instance n) (m : ℕ) :
    MeasurePreserving (ZeroSimulation.appendValues (m := m)) P.valuesLaw (P.appendZeros m).valuesLaw := by
  have hbase : MeasurePreserving (fun x : Fin n → ℝ => (x, fun _ : Fin m => (0 : ℝ)))
      P.valuesLaw (P.valuesLaw.prod (Measure.pi (fun _ : Fin m => Measure.dirac (0 : ℝ)))) := by
    refine ⟨by fun_prop, ?_⟩
    rw [pi_dirac_zero, Measure.prod_dirac]
  exact (measurePreserving_finAddCases P.law (fun _ : Fin m => Measure.dirac (0 : ℝ))).comp hbase

lemma appendClocks_measurePreserving (n m : ℕ) :
    MeasurePreserving (fun z : (Fin n → ℝ) × (Fin m → ℝ) => ZeroSimulation.appendClocks z.1 z.2)
      ((clocksLaw n).prod (clocksLaw m)) (clocksLaw (n + m)) := by
  have h := measurePreserving_finAddCases (fun _ : Fin n => uniformClock) (fun _ : Fin m => uniformClock)
  have he : (Fin.addCases (fun _ : Fin n => uniformClock) (fun _ : Fin m => uniformClock) :
      Fin (n + m) → Measure ℝ) = fun _ => uniformClock := by
    funext k
    induction k using Fin.addCases <;> simp
  rw [he] at h
  exact h

lemma maximum_appendValues (x : Fin n → ℝ) :
    maximum (ZeroSimulation.appendValues (m := m) x) = maximum x := by
  apply le_antisymm
  · apply maximum_le _ (maximum_nonnegative x)
    intro k
    induction k using Fin.addCases with
    | left i => simpa [ZeroSimulation.appendValues] using le_maximum x i
    | right j => simpa [ZeroSimulation.appendValues] using maximum_nonnegative x
  · apply maximum_le _ (maximum_nonnegative (ZeroSimulation.appendValues (m := m) x))
    intro i
    simpa [ZeroSimulation.appendValues] using
      le_maximum (ZeroSimulation.appendValues (m := m) x) (Fin.castAdd m i)

lemma appendZeros_integrable_maximum (P : Instance n) (m : ℕ)
    (hP : Integrable maximum P.valuesLaw) : Integrable maximum (P.appendZeros m).valuesLaw := by
  apply ((P.appendValues_measurePreserving m).integrable_comp measurable_maximum.aestronglyMeasurable).mp
  simpa only [Function.comp_def, maximum_appendValues] using hP

lemma appendZeros_expectedMaximum (P : Instance n) (m : ℕ) :
    (P.appendZeros m).expectedMaximum = P.expectedMaximum := by
  have h := integral_map (μ := P.valuesLaw) (P.appendValues_measurePreserving m).measurable.aemeasurable
    measurable_maximum.aestronglyMeasurable
  rw [(P.appendValues_measurePreserving m).map_eq] at h
  simpa only [expectedMaximum, maximum_appendValues] using h

variable {Seed : Type*} [MeasurableSpace Seed]

/-- The augmented online world reconstructed from a base world and zero clocks in its seed. -/
def augmentZeroWorld (ω : World n (Seed × (Fin m → ℝ))) : World (n + m) Seed :=
  (ZeroSimulation.appendValues ω.1, (ZeroSimulation.appendClocks ω.2.1 ω.2.2.2, ω.2.2.1))

lemma augmentZeroWorld_measurePreserving (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (m : ℕ) :
    MeasurePreserving (augmentZeroWorld (n := n) (m := m))
      (P.worldLaw (ν.prod (clocksLaw m))) ((P.appendZeros m).worldLaw ν) := by
  have h₁ := (MeasurePreserving.id P.valuesLaw).prod
    ((MeasurePreserving.id (clocksLaw n)).prod (Measure.measurePreserving_swap (μ := ν) (ν := clocksLaw m)))
  have h₂ := (MeasurePreserving.id P.valuesLaw).prod
    ((measurePreserving_prodAssoc (clocksLaw n) (clocksLaw m) ν).symm MeasurableEquiv.prodAssoc)
  have h₃ := (P.appendValues_measurePreserving m).prod
    ((appendClocks_measurePreserving n m).prod (MeasurePreserving.id ν))
  exact h₃.comp (h₂.comp h₁)

end Instance
namespace RandomizedPolicy

variable {n m : ℕ}

/-- Simulate all appended zero identities using independent policy randomness. -/
noncomputable def simulateZeros (π : RandomizedPolicy (n + m)) : RandomizedPolicy n where
  Seed := π.Seed × (Fin m → ℝ)
  seedLaw := π.seedLaw.prod (Instance.clocksLaw m)
  rule := ZeroSimulation.simulate π.rule
  measurable_rule := ZeroSimulation.simulate_isMeasurable π.rule π.measurable_rule

lemma simulateZeros_expectedReward (π : RandomizedPolicy (n + m)) (P : Instance n) :
    (simulateZeros π).expectedReward P = π.expectedReward (P.appendZeros m) := by
  have hmap := Instance.augmentZeroWorld_measurePreserving P π.seedLaw m
  have h := integral_map (μ := P.worldLaw (π.seedLaw.prod (Instance.clocksLaw m))) hmap.measurable.aemeasurable π.measurable_realizedReward.aestronglyMeasurable
  rw [hmap.map_eq] at h
  rw [expectedReward]
  calc
    ∫ ω, (simulateZeros π).realizedReward ω ∂P.worldLaw (simulateZeros π).seedLaw =
        ∫ ω, π.realizedReward (Instance.augmentZeroWorld ω) ∂P.worldLaw (π.seedLaw.prod (Instance.clocksLaw m)) := by
      apply integral_congr_ae
      filter_upwards [P.world_clocks_mem_unitInterval (π.seedLaw.prod (Instance.clocksLaw m))] with ω hω
      exact ZeroSimulation.reward_eq π.rule ω.2.2.1 ω.1 ω.2.1 ω.2.2.2 (fun i => (hω i).2)
    _ = π.expectedReward (P.appendZeros m) := h.symm

lemma simulateZeros_expectedDuration (π : RandomizedPolicy (n + m)) (P : Instance n) :
    π.expectedDuration (P.appendZeros m) ≤ (simulateZeros π).expectedDuration P := by
  have hmap := Instance.augmentZeroWorld_measurePreserving P π.seedLaw m
  have h := integral_map (μ := P.worldLaw (π.seedLaw.prod (Instance.clocksLaw m))) hmap.measurable.aemeasurable π.measurable_realizedDuration.aestronglyMeasurable
  rw [hmap.map_eq] at h
  change ∫ ω, π.realizedDuration ω ∂(P.appendZeros m).worldLaw π.seedLaw ≤ _
  rw [h]
  apply integral_mono_ae
    (hmap.integrable_comp_of_integrable (π.integrable_realizedDuration (P.appendZeros m)))
    ((simulateZeros π).integrable_realizedDuration P)
  exact Filter.Eventually.of_forall fun ω =>
    ZeroSimulation.stoppingTime_le_simulated π.rule ω.2.2.1 ω.1 ω.2.1 ω.2.2.2

lemma scalarObjective_le_simulateZeros (π : RandomizedPolicy (n + m)) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hc : 0 ≤ c) :
    π.scalarObjective (P.appendZeros m) w c ≤ (simulateZeros π).scalarObjective P w c := by
  rw [π.scalarObjective_eq (P.appendZeros m) (P.appendZeros_integrable_maximum m hP),
    (simulateZeros π).scalarObjective_eq P hP, simulateZeros_expectedReward]
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (simulateZeros_expectedDuration π P) hc)

end RandomizedPolicy

end ProphetSecretary.Model
