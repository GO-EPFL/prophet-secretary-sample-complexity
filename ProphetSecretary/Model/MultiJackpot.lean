import ProphetSecretary.Probability.JackpotCoupling
import ProphetSecretary.Model.ZeroSimulationProbability

/-!
# Independent dummy jackpots

Each appended dummy has its own Bernoulli flag. In the comparison execution all dummy
values are zero, but their identities and independent clocks are still observed.
-/

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped BigOperators Classical

namespace ProphetSecretary.Model

namespace Instance

variable {n : ℕ}

noncomputable def appendJackpots (P : Instance n) (N : ℕ) (p : unitInterval) (A : ℝ) (hA : 0 ≤ A) :
    Instance (n + N) where
  law := Fin.addCases P.law (fun _ => bernoulliMeasure A 0 p)
  probability j := by
    induction j using Fin.addCases with
    | left i => simpa using P.probability i
    | right j => simp only [Fin.addCases_right]; infer_instance
  nonnegative j := by
    induction j using Fin.addCases with
    | left i => simpa using P.nonnegative i
    | right j =>
      simp only [Fin.addCases_right, bernoulliMeasure_def, ae_add_measure_iff]
      exact ⟨Measure.ae_smul_measure (by simpa using hA) _, Measure.ae_smul_measure (by simp) _⟩

lemma appendJackpots_bounded (P : Instance n) (N : ℕ) (p : unitInterval) {A H : ℝ}
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H) :
    ∀ j, ∀ᵐ x ∂(P.appendJackpots N p A hA).law j, x ≤ H + A := by
  intro j
  induction j using Fin.addCases with
  | left i =>
    simpa only [appendJackpots, Fin.addCases_left] using
      (hbound i).mono (fun x hx => hx.trans (le_add_of_nonneg_right hA))
  | right j =>
    simp only [appendJackpots, Fin.addCases_right, bernoulliMeasure_def, ae_add_measure_iff]
    constructor
    · exact Measure.ae_smul_measure (by simp [hH]) _
    · exact Measure.ae_smul_measure (by simp [add_nonneg hH hA]) _

lemma appendJackpots_integrable_maximum (P : Instance n) (N : ℕ) (p : unitInterval) {A H : ℝ}
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H) :
    Integrable maximum (P.appendJackpots N p A hA).valuesLaw :=
  (P.appendJackpots N p A hA).integrable_maximum_of_bounded
    (P.appendJackpots_bounded N p hA hH hbound)

end Instance

namespace MultiJackpot

variable {n N : ℕ} {Seed : Type*} [MeasurableSpace Seed]

abbrev CouplingWorld (n N : ℕ) (Seed : Type*) :=
  (Fin N → Bool) × ((Fin n → ℝ) × ((Fin (n + N) → ℝ) × Seed))

noncomputable def couplingLaw (P : Instance n) (N : ℕ) (p : unitInterval) (ν : Measure Seed) :
    Measure (CouplingWorld n N Seed) :=
  (ProphetSecretary.Probability.jackpotCoins N p).prod
    (P.valuesLaw.prod ((Instance.clocksLaw (n + N)).prod ν))

instance couplingLaw_probability (P : Instance n) (N : ℕ) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (couplingLaw P N p ν) := by
  dsimp [couplingLaw]
  infer_instance

def jackpotValues (A : ℝ) (b : Fin N → Bool) (x : Fin n → ℝ) : Fin (n + N) → ℝ :=
  Fin.addCases x (fun j => if b j = true then A else 0)

def zeroWorld (z : CouplingWorld n N Seed) : World (n + N) Seed :=
  (ZeroSimulation.appendValues z.2.1, z.2.2)

def jackpotWorld (A : ℝ) (z : CouplingWorld n N Seed) : World (n + N) Seed :=
  (jackpotValues A z.1 z.2.1, z.2.2)

lemma bitRewards_measurePreserving (N : ℕ) (p : unitInterval) (A : ℝ) :
    MeasurePreserving (fun b : Fin N → Bool => fun j => if b j = true then A else (0 : ℝ))
      (ProphetSecretary.Probability.jackpotCoins N p) (Measure.pi (fun _ : Fin N => bernoulliMeasure A 0 p)) := by
  change MeasurePreserving _ (Measure.pi (fun _ : Fin N => bernoulliMeasure true false p)) _
  apply measurePreserving_pi (fun _ : Fin N => bernoulliMeasure true false p)
    (fun _ : Fin N => bernoulliMeasure A 0 p)
    (f := fun _ : Fin N => fun b : Bool => if b = true then A else (0 : ℝ))
  intro j
  refine ⟨measurable_of_finite _, ?_⟩
  simp only [map_bernoulliMeasure, ite_true, Bool.false_eq_true, ite_false]

lemma jackpotValues_measurePreserving (P : Instance n) (N : ℕ) (p : unitInterval) (A : ℝ) (hA : 0 ≤ A) :
    MeasurePreserving (fun z : (Fin N → Bool) × (Fin n → ℝ) => jackpotValues A z.1 z.2)
      ((ProphetSecretary.Probability.jackpotCoins N p).prod P.valuesLaw) (P.appendJackpots N p A hA).valuesLaw := by
  have h₁ := Measure.measurePreserving_swap (μ := ProphetSecretary.Probability.jackpotCoins N p) (ν := P.valuesLaw)
  have h₂ := (MeasurePreserving.id P.valuesLaw).prod (bitRewards_measurePreserving N p A)
  have h₃ := measurePreserving_finAddCases P.law (fun _ : Fin N => bernoulliMeasure A 0 p)
  exact h₃.comp (h₂.comp h₁)

lemma zeroWorld_measurePreserving (P : Instance n) (N : ℕ) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    MeasurePreserving (zeroWorld (n := n) (N := N)) (couplingLaw P N p ν)
      ((P.appendZeros N).worldLaw ν) := by
  exact ((P.appendValues_measurePreserving N).prod
    (MeasurePreserving.id ((Instance.clocksLaw (n + N)).prod ν))).comp measurePreserving_snd

lemma jackpotWorld_measurePreserving (P : Instance n) (N : ℕ) (p : unitInterval) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (A : ℝ) (hA : 0 ≤ A) :
    MeasurePreserving (jackpotWorld A) (couplingLaw P N p ν) ((P.appendJackpots N p A hA).worldLaw ν) := by
  have h₁ := (measurePreserving_prodAssoc (ProphetSecretary.Probability.jackpotCoins N p) P.valuesLaw
    ((Instance.clocksLaw (n + N)).prod ν)).symm MeasurableEquiv.prodAssoc
  exact ((jackpotValues_measurePreserving P N p A hA).prod
    (MeasurePreserving.id ((Instance.clocksLaw (n + N)).prod ν))).comp h₁

end MultiJackpot
end ProphetSecretary.Model
