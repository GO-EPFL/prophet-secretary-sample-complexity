import ProphetSecretary.Limiting.CountablePolicy
import ProphetSecretary.Probability.InfiniteErasure
import ProphetSecretary.Probability.ProductIndependentPairs

/-!
# The countable world with one individual kept pending

The auxiliary complete vector replaces only the candidate's value by zero
and its clock by the terminal time. Every other identity, including zero
observations, and the entire anonymous configuration are preserved. Joint
independence from the omitted value and clock follows from actual infinite
product erasure and independent policy randomness.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

def pendingIndividualWorld (i : ℕ) (z : (ℕ → ℝ) × ((ℕ → ℝ) × Seed)) :=
  (Function.update z.1 i 0,(Function.update z.2.1 i 1,z.2.2))

def keepIndividualPending (i : ℕ) (v : CompleteWorld Seed) : CompleteWorld Seed :=
  (v.1,pendingIndividualWorld i v.2)

def replaceIndividualClock (i : ℕ) (z : CompleteWorld Seed × ℝ) : CompleteWorld Seed :=
  (z.1.1,(z.1.2.1,(Function.update z.1.2.2.1 i z.2,z.1.2.2.2)))

variable [MeasurableSpace Seed]

lemma measurable_pendingIndividualWorld (i : ℕ) : Measurable (pendingIndividualWorld (Seed := Seed) i) :=
  ((Model.measurable_eraseCoordinate i (0 : ℝ)).comp measurable_fst).prodMk
    (((Model.measurable_eraseCoordinate i (1 : ℝ)).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))

lemma measurable_keepIndividualPending (i : ℕ) : Measurable (keepIndividualPending (Seed := Seed) i) :=
  measurable_fst.prodMk ((measurable_pendingIndividualWorld i).comp measurable_snd)

lemma pendingIndividualWorld_candidate_independent (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    IndepFun (pendingIndividualWorld i) (fun z : (ℕ → ℝ) × ((ℕ → ℝ) × Seed) => (z.1 i,z.2.1 i))
      (B.individualWorldLaw ν) := by
  have hX := ProphetSecretary.Probability.infinite_erasure_independent
    (fun j => (B.individuals j : Measure ℝ)) i (0 : ℝ)
  have hU := ProphetSecretary.Probability.infinite_erasure_independent
    (fun _ : ℕ => Model.Instance.uniformClock) i (1 : ℝ)
  have hUS := Model.indepFun_with_seed (Model.measurable_eraseCoordinate i (1 : ℝ))
    (measurable_pi_apply i) hU (ν := ν)
  exact ProphetSecretary.Probability.indepFun_product_pairs
    (μ := B.individualValuesLaw) (ν := individualClocksLaw.prod ν)
    (Model.measurable_eraseCoordinate i (0 : ℝ)) (measurable_pi_apply i)
    (((Model.measurable_eraseCoordinate i (1 : ℝ)).comp measurable_fst).prodMk measurable_snd)
    ((measurable_pi_apply i).comp measurable_fst) hX hUS

lemma keepIndividualPending_candidate_independent (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    IndepFun (keepIndividualPending i) (fun v : CompleteWorld Seed => (v.2.1 i,v.2.2.1 i))
      (B.completeWorldLaw ν) := by
  have hPair : Measurable (fun z : (ℕ → ℝ) × ((ℕ → ℝ) × Seed) => (z.1 i,z.2.1 i)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hRaw := Model.indepFun_with_seed (measurable_pendingIndividualWorld (Seed := Seed) i) hPair
    (pendingIndividualWorld_candidate_independent B ν i) (ν := B.bandConfigurationsLaw)
  have hSwap := Measure.measurePreserving_swap (μ := B.bandConfigurationsLaw) (ν := B.individualWorldLaw ν)
  have hLeft : Measurable (fun z : ((ℕ → ℝ) × ((ℕ → ℝ) × Seed)) × BandConfigurations =>
      (pendingIndividualWorld i z.1,z.2)) :=
    ((measurable_pendingIndividualWorld i).comp measurable_fst).prodMk measurable_snd
  have hRight := hPair.comp (measurable_fst : Measurable
    (fun z : ((ℕ → ℝ) × ((ℕ → ℝ) × Seed)) × BandConfigurations => z.1))
  have hPull := Model.indepFun_pullback hSwap hLeft hRight hRaw
  exact hPull.comp measurable_swap measurable_id

end ProphetSecretary.Limiting.CountableInstance
