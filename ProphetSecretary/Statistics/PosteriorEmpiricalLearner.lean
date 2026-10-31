import ProphetSecretary.Statistics.EmpiricalBlockPolicy
import ProphetSecretary.Statistics.PosteriorEmpiricalScalar

/-!
# An actual empirical learner at an observed posterior target

The prior and deployment index are fixed before training. The callback
uses only the reconstructed visible prefix, its selected empirical block,
and the observable target posterior. The last ONLINE column is always
filled with zero by prefix reconstruction. The hard budget and cap/zero
rules hold for every training outcome.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n m N : ℕ} [NeZero m]

lemma prefixLearner_policy_eq_comap {Seed : Type} [MeasurableSpace Seed]
    (N b k : ℕ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable) :
    (prefixLearner N b k ν π hπ).policy=
      π.comapSeed (fun p : Reservoir n (trainingLength N b k) × Seed => (extendTrainingPrefix n N b k p.1,p.2)) := by
  apply congrArg Policy.mk
  funext p t i x H
  rcases p with ⟨y,r⟩
  exact Learner.ofSamplePolicy_decide Seed ν (prefixSamplePolicy N b k π)
    (prefixSamplePolicy_isMeasurable N b k hπ) y r t i x H

noncomputable def posteriorEmpiricalPolicy (F : FinitePrior n) (N b k : ℕ)
    (e : Fin m → Fin (N+1)) (ρ : ℝ → ℝ) : Policy (ValueArray n N × Unit) n :=
  empiricalBlockPolicy e (fun p => F.posteriorEmpiricalScalar N b k ρ p.1)

lemma posteriorEmpiricalPolicy_isMeasurable (F : FinitePrior n) (N b k : ℕ)
    (e : Fin m → Fin (N+1)) {ρ : ℝ → ℝ} (hρ : Measurable ρ) :
    (F.posteriorEmpiricalPolicy N b k e ρ).IsMeasurable :=
  empiricalBlockPolicy_isMeasurable e ((F.measurable_posteriorEmpiricalScalar N b k hρ).comp measurable_fst)

noncomputable def posteriorEmpiricalLearner (F : FinitePrior n) (N b k : ℕ)
    (e : Fin m → Fin (N+1)) (ρ : ℝ → ℝ) (hρ : Measurable ρ) : Learner n (trainingLength N b k) :=
  prefixLearner N b k (Measure.dirac ()) (F.posteriorEmpiricalPolicy N b k e ρ)
    (F.posteriorEmpiricalPolicy_isMeasurable N b k e hρ)

lemma posteriorEmpiricalLearner_hardBudget (F : FinitePrior n) (N b k : ℕ)
    (e : Fin m → Fin (N+1)) (ρ : ℝ → ℝ) (hρ : Measurable ρ)
    (y : Reservoir n (trainingLength N b k)) (r : Unit) (i : Fin n) :
    requests (trainingTranscript (F.posteriorEmpiricalLearner N b k e ρ hρ).request r y) i≤trainingLength N b k :=
  prefixLearner_hardBudget N b k (Measure.dirac ()) _ _ y r i

lemma posteriorEmpiricalLearner_accepts_cap (F : FinitePrior n) (N b k : ℕ)
    (e : Fin m → Fin (N+1)) (ρ : ℝ → ℝ) (hρ : Measurable ρ) {hi : ℝ}
    (hhi : hi<1) (hRange : ∀ t∈Icc (0 : ℝ) 1, ρ t∈Icc (4/5 : ℝ) hi)
    (y : Reservoir n (trainingLength N b k)) (r : Unit) {t : ℝ} (ht : 0≤t) (i : Fin n) (H : History n) :
    (F.posteriorEmpiricalLearner N b k e ρ hρ).policy.decide (y,r) t i 1 H=true := by
  change (prefixLearner N b k (Measure.dirac ()) (F.posteriorEmpiricalPolicy N b k e ρ)
    (F.posteriorEmpiricalPolicy_isMeasurable N b k e hρ)).policy.decide (y,r) t i 1 H=true
  rw [prefixLearner_policy_eq_comap]
  have hZ := F.posteriorEmpiricalScalar_mem N b k hhi hRange (extendTrainingPrefix n N b k y)
  exact empiricalBlockPolicy_accepts_cap e (fun p : ValueArray n N × Unit => F.posteriorEmpiricalScalar N b k ρ p.1) (extendTrainingPrefix n N b k y,r) ht
    ((sub_nonneg.mpr hhi.le).trans hZ.1) hZ.2 i H

lemma posteriorEmpiricalLearner_rejects_zero (F : FinitePrior n) (N b k : ℕ)
    (e : Fin m → Fin (N+1)) (ρ : ℝ → ℝ) (hρ : Measurable ρ)
    (y : Reservoir n (trainingLength N b k)) (r : Unit) (t : ℝ) (i : Fin n) (H : History n) :
    (F.posteriorEmpiricalLearner N b k e ρ hρ).policy.decide (y,r) t i 0 H=false := by
  change (prefixLearner N b k (Measure.dirac ()) (F.posteriorEmpiricalPolicy N b k e ρ)
    (F.posteriorEmpiricalPolicy_isMeasurable N b k e hρ)).policy.decide (y,r) t i 0 H=false
  rw [prefixLearner_policy_eq_comap]
  exact empiricalBlockPolicy_rejects_zero e (fun p : ValueArray n N × Unit => F.posteriorEmpiricalScalar N b k ρ p.1) (extendTrainingPrefix n N b k y,r) t i H

end ProphetSecretary.Statistics.FinitePrior
