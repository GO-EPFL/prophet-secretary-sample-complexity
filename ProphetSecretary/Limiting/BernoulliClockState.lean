import ProphetSecretary.Limiting.BernoulliChildValueApproximation
import ProphetSecretary.Limiting.VirtualUnseenState

/-!
# Bernoulli continuation states along real and virtual clocks

The current original clocks are fixed while the independent virtual clocks
vary. The original unseen set is therefore fixed; the virtual set still
records every observed zero identity. The state-value error is uniform over
all original clock vectors and both retained and anonymous candidate types.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n q : ℕ}

noncomputable def retainedClockState (u : Fin n → ℝ) (t : ℝ) (candidate : Option (Fin n)) : Finset (Fin n) :=
  candidate.elim (Model.unseen (Model.history Finset.univ (fun _ => 0) u t))
    (fun i => (Model.unseen (Model.history Finset.univ (fun _ => 0) u t)).erase i)

noncomputable def virtualClockState (u : Fin n → ℝ) (t : ℝ) (candidate : Option (Fin n))
    (z : Fin q → ℝ) : Finset (Fin (n+q)) :=
  virtualContinuationState (fun _ => 0) (Model.ZeroSimulation.appendClocks u z) t candidate

lemma virtualClockState_retained (u : Fin n → ℝ) (t : ℝ) (candidate : Option (Fin n)) (z : Fin q → ℝ) :
    Model.retainedSet q (virtualClockState u t candidate z) = retainedClockState u t candidate := by
  rw [virtualClockState,virtualContinuationState_retained]
  simp only [Model.ZeroSimulation.appendClocks,Fin.addCases_left]
  rfl

lemma virtualClockState_count (u : Fin n → ℝ) (t : ℝ) (candidate : Option (Fin n)) (z : Fin q → ℝ) :
    (virtualSet n (virtualClockState u t candidate z)).card = virtualUnseenCount t z := by
  rw [virtualClockState,virtualContinuationState_virtual_count]
  simp only [Model.ZeroSimulation.appendClocks,Fin.addCases_right]

lemma measurable_virtualClockState (u : Fin n → ℝ) (t : ℝ) (candidate : Option (Fin n)) :
    Measurable (virtualClockState (q := q) u t candidate) := by
  have hU (i : Fin (n+q)) : Measurable (fun z : Fin q → ℝ => Model.ZeroSimulation.appendClocks u z i) := by
    induction i using Fin.addCases with
    | left i => simpa only [Model.ZeroSimulation.appendClocks,Fin.addCases_left] using
        (measurable_const : Measurable (fun _ : Fin q → ℝ => u i))
    | right j => simpa only [Model.ZeroSimulation.appendClocks,Fin.addCases_right] using (measurable_pi_apply j)
  have hS : Measurable (fun z : Fin q → ℝ =>
      Model.unseen (Model.history Finset.univ (fun _ => 0) (Model.ZeroSimulation.appendClocks u z) t)) :=
    Model.measurable_unseen.comp (Model.measurable_history Finset.univ (fun _ => measurable_const) hU measurable_const)
  cases candidate with
  | none => exact hS
  | some i => exact (measurable_of_countable (fun S : Finset (Fin (n+q)) => S.erase (i.castAdd q))).comp hS

/-- The finite design's continuation differs from the actual continuation by
its uniform Poisson error and the actual unseen-intensity-fraction error. -/
theorem FiniteIntensityHybridInstance.bernoulliClockState_value_error
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    (j : ℕ) (u : Fin n → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (candidate : Option (Fin n))
    (z : Fin (bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j) → ℝ)
    {w d : ℝ} (hw : 0 < w) (hd : 0 ≤ d) :
    let rate := (B.intensity : Measure ℝ).real univ
    let q := bernoulliMultiplicity rate j
    let p := bernoulliProbability rate measureReal_nonneg j
    let Q := finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) p q
    |Model.optimalScalarValue (Q.restrictTo (virtualClockState u t candidate z)) w d-
      ((B.restrictIndividuals (retainedClockState u t candidate)).remainingHorizon (remainingTime t)).optimalScalarValue w d| ≤
      B.bernoulliStateError w j+(w*(∫ x, x ∂(B.intensity : Measure ℝ)))*
        |(virtualUnseenCount t z : ℝ)/(q : ℝ)-(1-t)| := by
  have h := B.bernoulliChild_value_error ha hμ j (virtualClockState u t candidate z) (remainingTime t) hw hd
  dsimp only at h
  rw [virtualClockState_retained,virtualClockState_count] at h
  simp only [NNReal.coe_div,NNReal.coe_natCast,coe_remainingTime ht.2] at h
  convert h using 1
  ring

end ProphetSecretary.Limiting
