import ProphetSecretary.Statistics.StateFutureError
import ProphetSecretary.Model.Reindex

/-!
# Rescaling an actual unseen state back to physical elapsed time

The normalized future clock of an unseen identity is (U_i−t₀)/(1−t₀).
Its later pending set maps exactly to the original later pending set, and
optimized scalar continuation values agree after remaining-horizon rescaling.
The identities are pathwise and preserve the original identity embedding.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Probability

variable {n : ℕ}

noncomputable def normalizedStateClocks (t₀ : ℝ) (u : Fin n → ℝ) :
    Fin (pendingClockSet t₀ u).card → ℝ :=
  fun j => (u (Model.stateEmbedding (pendingClockSet t₀ u) j)-t₀)/(1-t₀)

lemma normalized_pendingClockSet_map {t₀ t : ℝ} (ht₀ : t₀ < 1) (htt₀ : t₀ ≤ t)
    (u : Fin n → ℝ) :
    (pendingClockSet ((t-t₀)/(1-t₀)) (normalizedStateClocks t₀ u)).map
      (Model.stateEmbedding (pendingClockSet t₀ u)) = pendingClockSet t u := by
  let A := pendingClockSet t₀ u
  have hd : 0 < 1-t₀ := sub_pos.mpr ht₀
  have hiff (j : Fin A.card) :
      (t-t₀)/(1-t₀) ≤ normalizedStateClocks t₀ u j ↔ t ≤ u (Model.stateEmbedding A j) := by
    change (t-t₀)/(1-t₀) ≤ (u (Model.stateEmbedding A j)-t₀)/(1-t₀) ↔ _
    rw [div_le_div_iff_of_pos_right hd, sub_le_sub_iff_right]
  apply Finset.ext
  intro i
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    exact (mem_pendingClockSet t u _).mpr ((hiff j).mp ((mem_pendingClockSet _ _ j).mp hj))
  · intro hi
    have hit := (mem_pendingClockSet t u i).mp hi
    have hiA : i ∈ A := (mem_pendingClockSet t₀ u i).mpr (htt₀.trans hit)
    let j := Model.stateIndex A i hiA
    have he : Model.stateEmbedding A j = i := Model.stateEmbedding_stateIndex A i hiA
    apply Finset.mem_map.mpr
    refine ⟨j,?_,he⟩
    apply (mem_pendingClockSet _ _ j).mpr
    exact (hiff j).mpr (by simpa only [he] using hit)

end ProphetSecretary.Probability

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem Instance.pendingContinuationValue_rescale (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z t₀ t : ℝ} (hz : 0 ≤ z)
    (ht₀ : t₀ < 1) (htt₀ : t₀ ≤ t) (ht1 : t ≤ 1) (u : Fin n → ℝ) :
    let A := ProphetSecretary.Probability.pendingClockSet t₀ u
    let s := (t-t₀)/(1-t₀)
    (P.restrictTo A).continuationValue
      (ProphetSecretary.Probability.pendingClockSet s (ProphetSecretary.Probability.normalizedStateClocks t₀ u))
      (1-s) 1 (z*(1-t₀)) =
      P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (1-t) 1 z := by
  let A := ProphetSecretary.Probability.pendingClockSet t₀ u
  let s := (t-t₀)/(1-t₀)
  let B := ProphetSecretary.Probability.pendingClockSet s (ProphetSecretary.Probability.normalizedStateClocks t₀ u)
  have hc : (z*(1-t₀))*(1-s) = z*(1-t) := by
    dsimp [s]
    field_simp [ne_of_gt (sub_pos.mpr ht₀)]
    ring
  change optimalScalarValue ((P.restrictTo A).restrictTo B) 1 ((z*(1-t₀))*(1-s)) = _
  rw [hc]
  have hv := P.optimalScalarValue_restrictTo_map (A.orderEmbOfFin rfl) B hP (by norm_num : (0 : ℝ) ≤ 1)
    (mul_nonneg hz (sub_nonneg.mpr ht1))
  change optimalScalarValue ((P.restrictTo A).restrictTo B) 1 (z*(1-t)) =
    optimalScalarValue (P.restrictTo (B.map (stateEmbedding A))) 1 (z*(1-t)) at hv
  have hm := ProphetSecretary.Probability.normalized_pendingClockSet_map ht₀ htt₀ u
  change B.map (stateEmbedding A) = _ at hm
  rw [hm] at hv
  exact hv

end ProphetSecretary.Model
