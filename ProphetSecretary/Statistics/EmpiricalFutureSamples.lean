import ProphetSecretary.Model.EmpiricalPolicy
import ProphetSecretary.Model.BellmanPathLoss
import ProphetSecretary.Model.TrainingCoordinates
import ProphetSecretary.Probability.RevealedCoordinates

/-!
# The empirical continuation uses only future sample rows

At a candidate arrival, every previously arrived identity has been removed from the
canonical continuation, including zero-valued observations. Masking all other training
coordinates leaves the continuation unchanged. This derives the reverse-process
adaptedness from the actual empirical law construction.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def futureSampleRows (u : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  (unseen (history Finset.univ (fun _ => 0) u (u i))).erase i

lemma mem_futureSampleRows (u : Fin n → ℝ) (i j : Fin n) :
    j ∈ futureSampleRows u i ↔ j ≠ i ∧ u i ≤ u j := by
  simp [futureSampleRows, unseen, history, not_lt]

lemma totalEmpiricalInstance_restrictTo_mask_samples
    (z : (Fin n × Fin k) → ℝ) (s : Finset (Fin n × Fin k)) (A : Finset (Fin n))
    (hA : ∀ i ∈ A, ∀ j : Fin k, (i, j) ∈ s) :
    (totalEmpiricalInstance (reservoirCoordinates.symm (ProphetSecretary.Probability.maskCoordinates s z))).restrictTo A =
      (totalEmpiricalInstance (reservoirCoordinates.symm z)).restrictTo A := by
  apply Instance.eq_of_law_eq
  funext q
  have hq : stateEmbedding A q ∈ A := A.orderEmbOfFin_mem rfl q
  change empiricalLaw (fun j => max 0 (ProphetSecretary.Probability.maskCoordinates s z (stateEmbedding A q, j))) =
    empiricalLaw (fun j => max 0 (z (stateEmbedding A q, j)))
  congr 1
  funext j
  rw [ProphetSecretary.Probability.maskCoordinates, if_pos (hA _ hq j)]

noncomputable def empiricalArrivalContinuation (w c : ℝ) (u : Fin n → ℝ) (i : Fin n)
    (z : (Fin n × Fin k) → ℝ) : ℝ :=
  (totalEmpiricalInstance (reservoirCoordinates.symm z)).continuationAtArrival w c (fun _ => 0) u i

lemma empiricalArrivalContinuation_mask (w c : ℝ) (u : Fin n → ℝ) (i : Fin n)
    (s : Finset (Fin n × Fin k)) (hfuture : ∀ q ∈ futureSampleRows u i, ∀ j : Fin k, (q, j) ∈ s)
    (z : (Fin n × Fin k) → ℝ) :
    empiricalArrivalContinuation w c u i (ProphetSecretary.Probability.maskCoordinates s z) =
      empiricalArrivalContinuation w c u i z := by
  unfold empiricalArrivalContinuation Instance.continuationAtArrival Instance.continuationValue
  exact congrArg (fun D : Instance (futureSampleRows u i).card =>
    optimalScalarValue D w (c * max 0 (1 - u i)))
    (totalEmpiricalInstance_restrictTo_mask_samples z s (futureSampleRows u i) hfuture)

lemma measurable_empiricalArrivalContinuation {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (u : Fin n → ℝ) (i : Fin n) :
    Measurable (empiricalArrivalContinuation (k := k) w c u i) := by
  have hθ := measurable_totalEmpirical_valueThreshold
    (y := fun z : (Fin n × Fin k) → ℝ => reservoirCoordinates.symm z)
    (w := fun _ => w) (c := fun _ => c) (t := fun _ => u i)
    (A := fun _ => unseen (history Finset.univ (fun _ => 0) u (u i))) (i := fun _ => i)
    (fun q j => measurable_pi_apply (q, j)) measurable_const measurable_const measurable_const
    measurable_const measurable_const (fun _ => hw) (fun _ => hc)
  convert hθ.const_mul w using 1
  funext z
  exact (totalEmpiricalInstance (reservoirCoordinates.symm z)).continuationAtArrival_eq_threshold hw c (fun _ => 0) u i

/-- Actual empirical reverse predictability; no policy or continuation independence
is taken as an interface assumption. The remaining hypothesis is only set inclusion. -/
lemma empiricalArrivalContinuation_revealed_measurable {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (u : Fin n → ℝ) (i : Fin n) (s : Finset (Fin n × Fin k))
    (hfuture : ∀ q ∈ futureSampleRows u i, ∀ j : Fin k, (q, j) ∈ s) :
    @Measurable (((Fin n × Fin k) → ℝ)) ℝ
      (ProphetSecretary.Probability.revealedCoordinateSigma s) Real.measurableSpace
      (empiricalArrivalContinuation (k := k) w c u i) :=
  ProphetSecretary.Probability.measurable_of_mask_invariant (measurable_empiricalArrivalContinuation hw hc u i)
    (empiricalArrivalContinuation_mask w c u i s hfuture)

end ProphetSecretary.Model
