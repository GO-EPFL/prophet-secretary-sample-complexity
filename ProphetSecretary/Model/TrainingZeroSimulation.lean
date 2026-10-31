import ProphetSecretary.Model.FullSamplingReduction
import ProphetSecretary.Model.ZeroSimulationProbability

/-!
# Removing zero identities from a learner

The base learner requests its full hard budget, reconstructs the original
learner's training transcript with deterministic-zero samples inserted, and
simulates the additional observable zero identities using independent clocks.
The sample and online law transports are proved separately.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n N k : ℕ}

lemma measurePreserving_finAddCases_general {A : Type*} [MeasurableSpace A]
    (μ : Fin n → Measure A) (ν : Fin N → Measure A)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)] :
    MeasurePreserving (fun z : (Fin n → A) × (Fin N → A) =>
      (Fin.addCases z.1 z.2 : Fin (n + N) → A))
      ((Measure.pi μ).prod (Measure.pi ν))
      (Measure.pi (Fin.addCases μ ν : Fin (n + N) → Measure A)) := by
  let ρ : Fin (n + N) → Measure A := Fin.addCases μ ν
  haveI : ∀ i, IsProbabilityMeasure (ρ i) := by
    intro i
    induction i using Fin.addCases with
    | left i => simpa [ρ] using (inferInstance : IsProbabilityMeasure (μ i))
    | right i => simpa [ρ] using (inferInstance : IsProbabilityMeasure (ν i))
  let σ : Fin n ⊕ Fin N → Measure A := Sum.elim μ ν
  haveI : ∀ i, IsProbabilityMeasure (σ i) := by intro i; cases i <;> dsimp [σ] <;> infer_instance
  have hsum := measurePreserving_sumPiEquivProdPi_symm σ
  have hfin := measurePreserving_piCongrLeft (α := fun _ : Fin (n + N) => A) ρ finSumFinEquiv
  have he : (fun j : Fin n ⊕ Fin N => ρ (finSumFinEquiv j)) = σ := by
    funext j
    cases j <;> simp [ρ, σ]
  rw [he] at hfin
  have h := hfin.comp hsum
  convert h using 1
  · funext z i
    induction i using Fin.addCases with
    | left i => simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]; rfl
    | right i => simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]; rfl
  · rfl

def appendZeroReservoir (y : Reservoir n k) : Reservoir (n + N) k :=
  Fin.addCases y (fun _ _ => 0)

lemma measurable_appendZeroReservoir : Measurable (@appendZeroReservoir n N k) := by
  apply measurable_pi_lambda
  intro i
  induction i using Fin.addCases with
  | left j =>
    simpa only [appendZeroReservoir, Fin.addCases_left] using
      (measurable_pi_apply j : Measurable (fun y : Reservoir n k => y j))
  | right j =>
    simpa only [appendZeroReservoir, Fin.addCases_right] using
      (measurable_const : Measurable (fun _ : Reservoir n k => fun _ : Fin k => (0 : ℝ)))

lemma Instance.appendZeroReservoir_measurePreserving (P : Instance n) :
    MeasurePreserving (@appendZeroReservoir n N k) (P.reservoirLaw k)
      ((P.appendZeros N).reservoirLaw k) := by
  let μ : Fin n → Measure (Fin k → ℝ) := fun i => Measure.pi (fun _ : Fin k => P.law i)
  let ν : Fin N → Measure (Fin k → ℝ) := fun _ => Measure.dirac (fun _ => (0 : ℝ))
  have hzero : Measure.pi ν = Measure.dirac (fun _ : Fin N => fun _ : Fin k => (0 : ℝ)) := by
    have h := Measure.pi_map_pi (μ := ν) (f := fun _ _ => fun _ : Fin k => (0 : ℝ))
      (fun _ => measurable_const.aemeasurable)
    simpa only [Measure.map_const, measure_univ, one_smul] using h.symm
  have hbase : MeasurePreserving (fun y : Reservoir n k => (y, fun _ : Fin N => fun _ : Fin k => (0 : ℝ)))
      (P.reservoirLaw k) ((Measure.pi μ).prod (Measure.pi ν)) := by
    refine ⟨measurable_id.prodMk measurable_const, ?_⟩
    rw [hzero, Measure.prod_dirac]
    rfl
  have h := (measurePreserving_finAddCases_general μ ν).comp hbase
  convert h using 1
  · rfl
  · unfold Instance.reservoirLaw
    congr 1
    funext i
    induction i using Fin.addCases with
    | left j => simp only [Instance.appendZeros, Fin.addCases_left, μ]
    | right j =>
      simpa only [Instance.appendZeros, Fin.addCases_right, ν] using Instance.pi_dirac_zero k

def Policy.comapSeed {A B : Type*} (σ : A → B) (π : Policy B n) : Policy A n where
  decide a := π.decide (σ a)

lemma Policy.comapSeed_isMeasurable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {σ : A → B} (hσ : Measurable σ) (π : Policy B n) (hπ : π.IsMeasurable) :
    (π.comapSeed σ).IsMeasurable := hπ.comp ((hσ.comp measurable_fst).prodMk measurable_snd)

lemma Policy.comapSeed_reward {A B : Type*} (σ : A → B) (π : Policy B n)
    (a : A) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    (π.comapSeed σ).reward a D x u = π.reward (σ a) D x u := rfl

lemma Policy.comapSeed_stoppingTime {A B : Type*} (σ : A → B) (π : Policy B n)
    (a : A) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    (π.comapSeed σ).stoppingTime a D x u = π.stoppingTime (σ a) D x u := rfl

namespace Learner

def zeroSimulationSeedMap (L : Learner (n + N) k)
    (p : Reservoir n k × (L.Seed × (Fin N → ℝ))) :
    (Reservoir (n + N) k × L.Seed) × (Fin N → ℝ) :=
  ((appendZeroReservoir p.1, p.2.1), p.2.2)

lemma measurable_zeroSimulationSeedMap (L : Learner (n + N) k) : Measurable L.zeroSimulationSeedMap :=
  ((measurable_appendZeroReservoir.comp measurable_fst).prodMk
    (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)

noncomputable def zeroSimulationSamplePolicy (L : Learner (n + N) k) :
    Policy (Reservoir n k × (L.Seed × (Fin N → ℝ))) n :=
  (ZeroSimulation.simulate L.policy).comapSeed L.zeroSimulationSeedMap

lemma zeroSimulationSamplePolicy_isMeasurable (L : Learner (n + N) k) :
    L.zeroSimulationSamplePolicy.IsMeasurable :=
  Policy.comapSeed_isMeasurable L.measurable_zeroSimulationSeedMap _
    (ZeroSimulation.simulate_isMeasurable L.policy L.policy_isMeasurable)

/-- A causal base learner, with the original adaptive transcript simulated from
the visible full-sampling transcript and deterministic-zero training values. -/
noncomputable def removeZeros (L : Learner (n + N) k) : Learner n k :=
  letI : IsProbabilityMeasure L.seedLaw := L.probability
  letI : IsProbabilityMeasure (Instance.clocksLaw N) := Instance.clocksLaw_probability (n := N)
  Learner.ofSamplePolicy (L.Seed × (Fin N → ℝ)) (L.seedLaw.prod (Instance.clocksLaw N))
    L.zeroSimulationSamplePolicy L.zeroSimulationSamplePolicy_isMeasurable

theorem removeZeros_policy (L : Learner (n + N) k) : L.removeZeros.policy = L.zeroSimulationSamplePolicy := by
  have heq : L.removeZeros.policy.decide = L.zeroSimulationSamplePolicy.decide := by
    funext p t i x H
    exact Learner.ofSamplePolicy_decide (L.Seed × (Fin N → ℝ))
      (L.seedLaw.prod (Instance.clocksLaw N)) L.zeroSimulationSamplePolicy
      L.zeroSimulationSamplePolicy_isMeasurable p.1 p.2 t i x H
  exact congrArg Policy.mk heq

lemma zeroSimulationSeedMap_measurePreserving (L : Learner (n + N) k) (P : Instance n) :
    MeasurePreserving L.zeroSimulationSeedMap
      ((P.reservoirLaw k).prod (L.seedLaw.prod (Instance.clocksLaw N)))
      ((((P.appendZeros N).reservoirLaw k).prod L.seedLaw).prod (Instance.clocksLaw N)) := by
  have hassoc := (measurePreserving_prodAssoc (P.reservoirLaw k) L.seedLaw (Instance.clocksLaw N)).symm
    MeasurableEquiv.prodAssoc
  have hpad := ((P.appendZeroReservoir_measurePreserving (N := N) (k := k)).prod
    (MeasurePreserving.id L.seedLaw)).prod (MeasurePreserving.id (Instance.clocksLaw N))
  exact hpad.comp hassoc

def zeroSimulationWorldMap (L : Learner (n + N) k)
    (ω : World n (Reservoir n k × (L.Seed × (Fin N → ℝ)))) :
    World n ((Reservoir (n + N) k × L.Seed) × (Fin N → ℝ)) :=
  (ω.1, (ω.2.1, L.zeroSimulationSeedMap ω.2.2))

lemma zeroSimulationWorldMap_measurePreserving (L : Learner (n + N) k) (P : Instance n) :
    MeasurePreserving L.zeroSimulationWorldMap
      (P.worldLaw ((P.reservoirLaw k).prod (L.seedLaw.prod (Instance.clocksLaw N))))
      (P.worldLaw ((((P.appendZeros N).reservoirLaw k).prod L.seedLaw).prod (Instance.clocksLaw N))) :=
  (MeasurePreserving.id P.valuesLaw).prod
    ((MeasurePreserving.id (Instance.clocksLaw n)).prod (L.zeroSimulationSeedMap_measurePreserving P))

/-- Removing zero identities preserves the learner's expected reward, including
training and online randomness under their actual independent laws. -/
theorem removeZeros_expectedReward (L : Learner (n + N) k) (P : Instance n) :
    L.removeZeros.expectedReward P = L.expectedReward (P.appendZeros N) := by
  let π := L.randomizedPolicy (P.appendZeros N)
  let ρ := π.simulateZeros
  have hmap := L.zeroSimulationWorldMap_measurePreserving P
  have heq := integral_map (μ := P.worldLaw ((P.reservoirLaw k).prod
    (L.seedLaw.prod (Instance.clocksLaw N)))) hmap.measurable.aemeasurable
      ρ.measurable_realizedReward.aestronglyMeasurable
  rw [hmap.map_eq] at heq
  have htransport : L.removeZeros.expectedReward P = ρ.expectedReward P := by
    change (∫ ω : World n (Reservoir n k × (L.Seed × (Fin N → ℝ))),
      L.removeZeros.policy.reward ω.2.2 Finset.univ ω.1 ω.2.1
        ∂P.worldLaw ((P.reservoirLaw k).prod (L.seedLaw.prod (Instance.clocksLaw N)))) = _
    rw [L.removeZeros_policy]
    exact heq.symm
  exact htransport.trans (π.simulateZeros_expectedReward P)

lemma removeZeros_expectedDuration_eq (L : Learner (n + N) k) (P : Instance n) :
    (L.removeZeros.randomizedPolicy P).expectedDuration P =
      (L.randomizedPolicy (P.appendZeros N)).simulateZeros.expectedDuration P := by
  let ρ := (L.randomizedPolicy (P.appendZeros N)).simulateZeros
  have hmap := L.zeroSimulationWorldMap_measurePreserving P
  have heq := integral_map (μ := P.worldLaw ((P.reservoirLaw k).prod
    (L.seedLaw.prod (Instance.clocksLaw N)))) hmap.measurable.aemeasurable
      ρ.measurable_realizedDuration.aestronglyMeasurable
  rw [hmap.map_eq] at heq
  change (∫ ω : World n (Reservoir n k × (L.Seed × (Fin N → ℝ))),
      L.removeZeros.policy.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
        ∂P.worldLaw ((P.reservoirLaw k).prod (L.seedLaw.prod (Instance.clocksLaw N)))) = _
  rw [L.removeZeros_policy]
  exact heq.symm

/-- Simulated zero selections are replaced by waiting, so expected duration can
only increase. No identity observation is discarded during the simulation. -/
theorem removeZeros_meanDuration (L : Learner (n + N) k) (P : Instance n) :
    L.meanDuration (P.appendZeros N) ≤ L.removeZeros.meanDuration P := by
  change (L.randomizedPolicy (P.appendZeros N)).expectedDuration (P.appendZeros N) ≤
    (L.removeZeros.randomizedPolicy P).expectedDuration P
  rw [L.removeZeros_expectedDuration_eq]
  exact (L.randomizedPolicy (P.appendZeros N)).simulateZeros_expectedDuration P

theorem removeZeros_scalarObjective (L : Learner (n + N) k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hc : 0 ≤ c) :
    (L.randomizedPolicy (P.appendZeros N)).scalarObjective (P.appendZeros N) w c ≤
      (L.removeZeros.randomizedPolicy P).scalarObjective P w c := by
  rw [(L.randomizedPolicy (P.appendZeros N)).scalarObjective_eq (P.appendZeros N)
      (P.appendZeros_integrable_maximum N hP),
    (L.removeZeros.randomizedPolicy P).scalarObjective_eq P hP]
  have hR : (L.removeZeros.randomizedPolicy P).expectedReward P =
      (L.randomizedPolicy (P.appendZeros N)).expectedReward (P.appendZeros N) := L.removeZeros_expectedReward P
  rw [hR]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (L.removeZeros_meanDuration P) hc)

theorem removeZeros_guarantees (L : Learner (n + N) k) {ρ : ℝ} (hGuarantee : L.Guarantees ρ) :
    L.removeZeros.Guarantees ρ := by
  intro P hP
  rw [L.removeZeros_expectedReward]
  have hp : (P.appendZeros N).HasPositiveFiniteMaximum :=
    ⟨P.appendZeros_integrable_maximum N hP.1, by rw [P.appendZeros_expectedMaximum]; exact hP.2⟩
  have h := hGuarantee (P.appendZeros N) hp
  rwa [P.appendZeros_expectedMaximum] at h

theorem removeZeros_hardBudget (L : Learner (n + N) k) (y : Reservoir n k)
    (r : L.Seed × (Fin N → ℝ)) (i : Fin n) :
    requests (trainingTranscript L.removeZeros.request r y) i ≤ k :=
  L.removeZeros.hard_budget r y i

end Learner
end ProphetSecretary.Model
