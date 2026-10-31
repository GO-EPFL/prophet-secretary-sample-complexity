import ProphetSecretary.Model.ZeroSimulationExactDuration

/-!
# Complete-vector score expectations through causal zero simulation

Scores use only the original complete offer vector. The padded zero clocks
remain independent internal policy randomness. Product integrability is
explicit; reward always transports exactly, and elapsed duration transports
exactly when no padded-zero action occurs.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace ProphetSecretary.Model.RandomizedPolicy
variable {n m : ℕ}

lemma simulateZeros_score_reward (π : RandomizedPolicy (n+m)) (P : Instance n)
    (s : (Fin n → ℝ) → ℝ) (hs : Measurable s)
    (hInt : Integrable (fun ω : π.World => s (fun i => ω.1 (i.castAdd m))*π.realizedReward ω)
      ((P.appendZeros m).worldLaw π.seedLaw)) :
    Integrable (fun ω : π.simulateZeros.World => s ω.1*π.simulateZeros.realizedReward ω) (P.worldLaw π.simulateZeros.seedLaw) ∧
      (∫ ω : π.simulateZeros.World, s ω.1*π.simulateZeros.realizedReward ω ∂P.worldLaw π.simulateZeros.seedLaw)=
        ∫ ω : π.World, s (fun i => ω.1 (i.castAdd m))*π.realizedReward ω ∂(P.appendZeros m).worldLaw π.seedLaw := by
  have hMP := P.augmentZeroWorld_measurePreserving π.seedLaw m
  have hProj : Measurable (fun ω : π.World => fun i : Fin n => ω.1 (i.castAdd m)) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply (i.castAdd m)).comp measurable_fst)
  have hMeas := (hs.comp hProj).mul π.measurable_realizedReward
  have hEq : (fun ω : π.simulateZeros.World => s ω.1*π.simulateZeros.realizedReward ω) =ᵐ[P.worldLaw π.simulateZeros.seedLaw]
      (fun ω => s (fun i => (Instance.augmentZeroWorld ω).1 (i.castAdd m))*π.realizedReward (Instance.augmentZeroWorld ω)) := by
    filter_upwards [P.world_clocks_mem_unitInterval (π.seedLaw.prod (Instance.clocksLaw m))] with ω hu
    have hBase : (fun i : Fin n => (Instance.augmentZeroWorld ω).1 (i.castAdd m))=ω.1 := by
      funext i
      simp only [Instance.augmentZeroWorld,ZeroSimulation.appendValues,Fin.addCases_left]
    have hR : π.simulateZeros.realizedReward ω=π.realizedReward (Instance.augmentZeroWorld ω) :=
      ZeroSimulation.reward_eq π.rule ω.2.2.1 ω.1 ω.2.1 ω.2.2.2 (fun i => (hu i).2)
    rw [hBase,hR]
  refine ⟨(hMP.integrable_comp_of_integrable hInt).congr hEq.symm,?_⟩
  exact (integral_congr_ae hEq).trans (hMP.hasLaw.integral_comp hMeas.aestronglyMeasurable)

lemma simulateZeros_score_duration (π : RandomizedPolicy (n+m)) (P : Instance n)
    (hZero : ∀ᵐ ω ∂(P.appendZeros m).worldLaw π.seedLaw, ∀ j : Fin m,
      π.rule.action ω.2.2 Finset.univ ω.1 ω.2.1 (j.natAdd n)≠true)
    (s : (Fin n → ℝ) → ℝ) (hs : Measurable s)
    (hInt : Integrable (fun ω : π.World => s (fun i => ω.1 (i.castAdd m))*π.realizedDuration ω)
      ((P.appendZeros m).worldLaw π.seedLaw)) :
    Integrable (fun ω : π.simulateZeros.World => s ω.1*π.simulateZeros.realizedDuration ω) (P.worldLaw π.simulateZeros.seedLaw) ∧
      (∫ ω : π.simulateZeros.World, s ω.1*π.simulateZeros.realizedDuration ω ∂P.worldLaw π.simulateZeros.seedLaw)=
        ∫ ω : π.World, s (fun i => ω.1 (i.castAdd m))*π.realizedDuration ω ∂(P.appendZeros m).worldLaw π.seedLaw := by
  have hMP := P.augmentZeroWorld_measurePreserving π.seedLaw m
  have hNo := hMP.quasiMeasurePreserving.ae hZero
  have hProj : Measurable (fun ω : π.World => fun i : Fin n => ω.1 (i.castAdd m)) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply (i.castAdd m)).comp measurable_fst)
  have hMeas := (hs.comp hProj).mul π.measurable_realizedDuration
  have hEq : (fun ω : π.simulateZeros.World => s ω.1*π.simulateZeros.realizedDuration ω) =ᵐ[P.worldLaw π.simulateZeros.seedLaw]
      (fun ω => s (fun i => (Instance.augmentZeroWorld ω).1 (i.castAdd m))*π.realizedDuration (Instance.augmentZeroWorld ω)) := by
    filter_upwards [hNo] with ω hω
    have hBase : (fun i : Fin n => (Instance.augmentZeroWorld ω).1 (i.castAdd m))=ω.1 := by
      funext i
      simp only [Instance.augmentZeroWorld,ZeroSimulation.appendValues,Fin.addCases_left]
    have hT : π.simulateZeros.realizedDuration ω=π.realizedDuration (Instance.augmentZeroWorld ω) :=
      (ZeroSimulation.stoppingTime_eq_simulated_of_no_zero_action π.rule ω.2.2.1 ω.1 ω.2.1 ω.2.2.2 hω).symm
    rw [hBase,hT]
  refine ⟨(hMP.integrable_comp_of_integrable hInt).congr hEq.symm,?_⟩
  exact (integral_congr_ae hEq).trans (hMP.hasLaw.integral_comp hMeas.aestronglyMeasurable)
end ProphetSecretary.Model.RandomizedPolicy
