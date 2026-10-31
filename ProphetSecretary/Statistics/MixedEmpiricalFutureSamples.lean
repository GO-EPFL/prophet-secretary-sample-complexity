import ProphetSecretary.Model.MixedEmpiricalThresholdMeasurability
import ProphetSecretary.Statistics.EmpiricalFutureSamples

/-!
# Future-row predictability with exact known marginals

Only unknown unseen identities require retained sample rows. Known identities
use their fixed laws, so masking even their entire sample rows has no effect.
This establishes the actual reverse-reveal measurability needed for zero-jump
known rows and fresh unknown rows.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma mixedEmpiricalInstance_restrictTo_mask_samples (P : Instance n) (known : Finset (Fin n))
    (a : (Fin n × Fin k) → ℝ) (s : Finset (Fin n × Fin k)) (A : Finset (Fin n))
    (hA : ∀ i∈A, i∉known → ∀ l : Fin k, (i,l)∈s) :
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm (ProphetSecretary.Probability.maskCoordinates s a))).restrictTo A =
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).restrictTo A := by
  apply Instance.eq_of_law_eq
  funext j
  have hj : stateEmbedding A j∈A := A.orderEmbOfFin_mem rfl j
  by_cases hk : stateEmbedding A j∈known
  · change (if stateEmbedding A j∈known then _ else _) = (if stateEmbedding A j∈known then _ else _)
    simp only [if_pos hk]
  · change (if stateEmbedding A j∈known then _ else _) = (if stateEmbedding A j∈known then _ else _)
    simp only [if_neg hk]
    change empiricalLaw (fun l => max 0 (ProphetSecretary.Probability.maskCoordinates s a (stateEmbedding A j,l))) =
      empiricalLaw (fun l => max 0 (a (stateEmbedding A j,l)))
    congr 1
    funext l
    rw [ProphetSecretary.Probability.maskCoordinates,if_pos (hA _ hj hk l)]

noncomputable def mixedArrivalContinuation (P : Instance n) (known : Finset (Fin n))
    (w c : ℝ) (u : Fin n → ℝ) (i : Fin n) (a : (Fin n × Fin k) → ℝ) : ℝ :=
  (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).continuationAtArrival w c (fun _ => 0) u i

lemma mixedArrivalContinuation_mask (P : Instance n) (known : Finset (Fin n))
    (w c : ℝ) (u : Fin n → ℝ) (i : Fin n) (s : Finset (Fin n × Fin k))
    (hfuture : ∀ q∈futureSampleRows u i, q∉known → ∀ l : Fin k, (q,l)∈s)
    (a : (Fin n × Fin k) → ℝ) :
    mixedArrivalContinuation P known w c u i (ProphetSecretary.Probability.maskCoordinates s a) =
      mixedArrivalContinuation P known w c u i a := by
  unfold mixedArrivalContinuation Instance.continuationAtArrival Instance.continuationValue
  exact congrArg (fun Q : Instance (futureSampleRows u i).card =>
    optimalScalarValue Q w (c*max 0 (1-u i)))
    (mixedEmpiricalInstance_restrictTo_mask_samples P known a s (futureSampleRows u i) hfuture)

lemma measurable_mixedArrivalContinuation (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {w c : ℝ} (hw : 0<w) (hc : 0≤c) (u : Fin n → ℝ) (i : Fin n) :
    Measurable (mixedArrivalContinuation (k:=k) P known w c u i) := by
  have hθ := measurable_mixedEmpirical_valueThreshold P hP known
    (y:=fun a : (Fin n × Fin k) → ℝ => reservoirCoordinates.symm a)
    (w:=fun _ => w) (c:=fun _ => c) (t:=fun _ => u i)
    (A:=fun _ => unseen (history Finset.univ (fun _ => 0) u (u i))) (i:=fun _ => i)
    (fun j l => measurable_pi_apply (j,l)) measurable_const measurable_const measurable_const
    measurable_const measurable_const (fun _ => hw) (fun _ => hc)
  convert hθ.const_mul w using 1
  funext a
  exact (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).continuationAtArrival_eq_threshold
    hw c (fun _ => 0) u i

lemma mixedArrivalContinuation_revealed_measurable (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {w c : ℝ} (hw : 0<w) (hc : 0≤c) (u : Fin n → ℝ) (i : Fin n) (s : Finset (Fin n × Fin k))
    (hfuture : ∀ q∈futureSampleRows u i, q∉known → ∀ l : Fin k, (q,l)∈s) :
    @Measurable (((Fin n × Fin k) → ℝ)) ℝ (ProphetSecretary.Probability.revealedCoordinateSigma s)
      Real.measurableSpace (mixedArrivalContinuation (k:=k) P known w c u i) :=
  ProphetSecretary.Probability.measurable_of_mask_invariant (measurable_mixedArrivalContinuation P hP known hw hc u i)
    (mixedArrivalContinuation_mask P known w c u i s hfuture)

end ProphetSecretary.Model
