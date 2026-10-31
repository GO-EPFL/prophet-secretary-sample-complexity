import ProphetSecretary.Model.ScalarBands
import ProphetSecretary.Statistics.RestrictedTrainingState

/-!
# Candidate exclusion for the actual continuation threshold

After fixing a candidate's arrival time, its continuation depends on exactly
the other identities still pending. Restriction to all other identities and
then their pending set agrees with the original restriction, including every
zero-valued observation. Candidate value and its sample row are absent from
the resulting law; a training-selected scalar remains a separate fixed input.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma pending_otherIdentities_map (u : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    (ProphetSecretary.Probability.pendingClockSet t (u ∘ stateEmbedding (Finset.univ.erase i))).map
      (stateEmbedding (Finset.univ.erase i)) = otherUnseen u i t := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  apply Finset.ext
  intro j
  constructor
  · intro hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hj
    have hkA := stateEmbedding_mem A k
    have hkt := (ProphetSecretary.Probability.mem_pendingClockSet t (u ∘ stateEmbedding A) k).mp hk
    exact Finset.mem_filter.mpr ⟨hkA,hkt⟩
  · intro hj
    obtain ⟨hjA,hjt⟩ := Finset.mem_filter.mp hj
    let k := stateIndex A j hjA
    have he : stateEmbedding A k=j := stateEmbedding_stateIndex A j hjA
    apply Finset.mem_map.mpr
    refine ⟨k,?_,he⟩
    apply (ProphetSecretary.Probability.mem_pendingClockSet t (u ∘ stateEmbedding A) k).mpr
    simpa only [Function.comp_apply,he] using hjt

/-- The physical threshold after candidate replacement is the scalar value of
an actual other-variable instance. This is an analytical identity of values. -/
theorem Instance.continuationAtArrival_eq_otherPending (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0≤z)
    (x u : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    P.continuationAtArrival 1 z x (Function.update u i t) i =
      (P.restrictTo (Finset.univ.erase i)).continuationValue
        (ProphetSecretary.Probability.pendingClockSet t (u ∘ stateEmbedding (Finset.univ.erase i)))
        (max 0 (1-t)) 1 z := by
  unfold Instance.continuationAtArrival
  rw [Function.update_self,unseen_replaceClock_erase]
  unfold Instance.continuationValue
  let A := (Finset.univ : Finset (Fin n)).erase i
  let B := ProphetSecretary.Probability.pendingClockSet t (u ∘ stateEmbedding A)
  have h := P.optimalScalarValue_restrictTo_map (A.orderEmbOfFin rfl) B hP (w:=1) (c:=z*max 0 (1-t)) zero_le_one
    (mul_nonneg hz (le_max_left 0 (1-t)))
  change optimalScalarValue ((P.restrictTo A).restrictTo B) 1 (z*max 0 (1-t)) =
    optimalScalarValue (P.restrictTo (B.map (stateEmbedding A))) 1 (z*max 0 (1-t)) at h
  rw [pending_otherIdentities_map u i t] at h
  exact h.symm

/-- Empirical continuation uses only the other sample rows, once the scalar is
held fixed. No centering statement is made after selecting that scalar. -/
theorem empiricalArrivalContinuation_eq_otherPending {k : ℕ} [NeZero k]
    (a : (Fin n × Fin k) → ℝ) {z : ℝ} (hz : 0≤z) (u : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    (totalEmpiricalInstance (reservoirCoordinates.symm a)).continuationAtArrival 1 z (fun _ => 0) (Function.update u i t) i =
      (totalEmpiricalInstance (reservoirCoordinates.symm (restrictTrainingCoordinates (Finset.univ.erase i) a))).continuationValue
        (ProphetSecretary.Probability.pendingClockSet t (u ∘ stateEmbedding (Finset.univ.erase i)))
        (max 0 (1-t)) 1 z := by
  rw [(totalEmpiricalInstance (reservoirCoordinates.symm a)).continuationAtArrival_eq_otherPending
    (totalEmpiricalInstance_integrable _) hz (fun _ => 0) u i t,
    totalEmpiricalInstance_restrictTo_coordinates]

end ProphetSecretary.Model
