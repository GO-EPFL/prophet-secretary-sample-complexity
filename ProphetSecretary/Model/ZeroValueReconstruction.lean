import ProphetSecretary.Model.ZeroSimulationProbability

/-!
# Reconstructing a padded complete value vector

All appended coordinates equal zero on the actual product law. Projection
onto the original value vector and deterministic zero padding therefore
reconstruct the complete vector almost surely. This is an analytical value
identity and does not erase zero-valued arrival observations from a policy.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model.Instance
variable {n m : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma appendZeros_values_reconstruct_ae (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂(P.appendZeros m).worldLaw ν,
      ZeroSimulation.appendValues (fun i : Fin n => ω.1 (i.castAdd m))=ω.1 := by
  have hZeros : ∀ᵐ ω ∂(P.appendZeros m).worldLaw ν, ∀ j : Fin m, ω.1 (j.natAdd n)=0 := by
    rw [ae_all_iff]
    intro j
    have hz : ∀ᵐ x ∂(P.appendZeros m).law (j.natAdd n), x=0 := by simp [Instance.appendZeros]
    exact ((measurePreserving_eval (P.appendZeros m).law (j.natAdd n)).comp
      (measurePreserving_fst (μ := (P.appendZeros m).valuesLaw)
        (ν := (Instance.clocksLaw (n+m)).prod ν))).quasiMeasurePreserving.ae hz
  filter_upwards [hZeros] with ω hω
  funext k
  induction k using Fin.addCases with
  | left i => simp only [ZeroSimulation.appendValues,Fin.addCases_left]
  | right j =>
    simp only [ZeroSimulation.appendValues,Fin.addCases_right]
    exact (hω j).symm
end ProphetSecretary.Model.Instance
