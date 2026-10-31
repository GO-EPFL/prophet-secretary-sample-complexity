import ProphetSecretary.Model.Continuation
import Mathlib.Order.Fin.Basic

/-!
# Relabeling finite states

Optimal scalar values do not depend on the finite enumeration of identities.
The policy simulations behind restriction provide both directions, over the
full randomized online policy class.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {m n : ℕ}

namespace Instance

lemma restrictBy_equiv_inverse (P : Instance n) (e : Fin m ≃ Fin n) :
    (P.restrictBy e.toEmbedding).restrictBy e.symm.toEmbedding = P := by
  apply eq_of_law_eq
  funext i
  change P.law (e (e.symm i)) = P.law i
  rw [e.apply_symm_apply]

lemma optimalScalarValue_restrictBy_equiv (P : Instance n) (e : Fin m ≃ Fin n)
    (hP : Integrable maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue (P.restrictBy e.toEmbedding) w c = optimalScalarValue P w c := by
  apply le_antisymm (optimalScalarValue_restrictBy_le P e.toEmbedding hP hw hc)
  have h := optimalScalarValue_restrictBy_le (P.restrictBy e.toEmbedding) e.symm.toEmbedding
    (P.restrictBy_integrable_maximum e.toEmbedding hP) hw hc
  rw [P.restrictBy_equiv_inverse e] at h
  exact h

lemma optimalScalarValue_eq_of_law_equiv (P : Instance n) (Q : Instance m)
    (e : Fin m ≃ Fin n) (he : ∀ i, Q.law i = P.law (e i))
    (hP : Integrable maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue Q w c = optimalScalarValue P w c := by
  have hQ : Q = P.restrictBy e.toEmbedding := eq_of_law_eq (funext he)
  rw [hQ]
  exact P.optimalScalarValue_restrictBy_equiv e hP hw hc

end Instance

/-- Sorting a state and then applying an increasing identity embedding gives
the same original labels as sorting its image state. -/
lemma stateEmbedding_map (e : Fin m ↪o Fin n) (A : Finset (Fin m)) (j : Fin A.card) :
    stateEmbedding (A.map e.toEmbedding) (Fin.cast (Finset.card_map e.toEmbedding).symm j) =
      e (stateEmbedding A j) := by
  have he : (fun j : Fin A.card ↦ e (A.orderEmbOfFin rfl j)) =
      (A.map e.toEmbedding).orderEmbOfFin (Finset.card_map e.toEmbedding) := by
    apply Finset.orderEmbOfFin_unique
    · intro k
      exact Finset.mem_map.mpr ⟨A.orderEmbOfFin rfl k, A.orderEmbOfFin_mem rfl k, rfl⟩
    · exact e.strictMono.comp (A.orderEmbOfFin rfl).strictMono
  change (A.map e.toEmbedding).orderEmbOfFin rfl (Fin.cast (Finset.card_map e.toEmbedding).symm j) = _
  calc
    _ = (A.map e.toEmbedding).orderEmbOfFin (Finset.card_map e.toEmbedding) j :=
      (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff
        (h := rfl) (h' := Finset.card_map e.toEmbedding)
        (i := Fin.cast (Finset.card_map e.toEmbedding).symm j) (j := j)).mpr rfl
    _ = _ := (congrFun he j).symm

/-- Continuation values commute with increasing identity embeddings. -/
lemma Instance.optimalScalarValue_restrictTo_map (P : Instance n) (e : Fin m ↪o Fin n)
    (A : Finset (Fin m)) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue ((P.restrictBy e.toEmbedding).restrictTo A) w c =
      optimalScalarValue (P.restrictTo (A.map e.toEmbedding)) w c := by
  let φ : Fin A.card ≃ Fin (A.map e.toEmbedding).card :=
    (Fin.castOrderIso (Finset.card_map e.toEmbedding).symm).toEquiv
  apply P.restrictTo (A.map e.toEmbedding) |>.optimalScalarValue_eq_of_law_equiv
    ((P.restrictBy e.toEmbedding).restrictTo A) φ
  · intro j
    change P.law (e (stateEmbedding A j)) = P.law (stateEmbedding (A.map e.toEmbedding) (φ j))
    exact congrArg P.law (stateEmbedding_map e A j).symm
  · exact P.restrictTo_integrable_maximum (A.map e.toEmbedding) hP
  · exact hw
  · exact hc

/-- Value thresholds commute with increasing relabeling of an unseen state. -/
lemma Instance.valueThreshold_restrictBy (P : Instance n) (e : Fin m ↪o Fin n)
    (A : Finset (Fin m)) (k : Fin m) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (t : ℝ) :
    (P.restrictBy e.toEmbedding).valueThreshold w c A t k =
      P.valueThreshold w c (A.map e.toEmbedding) t (e k) := by
  unfold Instance.valueThreshold Instance.continuationValue
  have h := P.optimalScalarValue_restrictTo_map e (A.erase k) hP hw
    (mul_nonneg hc (le_max_left 0 (1 - t)))
  rw [Finset.map_erase] at h
  exact congrArg (fun v : ℝ ↦ v / w) h

/-- Restore elapsed time after a prefix. The new duration coefficient is
`c(1-s)`, while the reward coefficient is unchanged. -/
lemma Instance.valueThreshold_after_elapsed (P : Instance n) (A : Finset (Fin n))
    (i : Fin n) (w c s t : ℝ) (hs : s ≤ 1) :
    P.valueThreshold w c A (s + (1 - s) * t) i =
      P.valueThreshold w (c * (1 - s)) A t i := by
  have harg : 1 - (s + (1 - s) * t) = (1 - s) * (1 - t) := by ring
  have hmax : max 0 ((1 - s) * (1 - t)) = (1 - s) * max 0 (1 - t) := by
    simpa only [mul_zero] using (mul_max_of_nonneg 0 (1 - t) (sub_nonneg.mpr hs)).symm
  unfold Instance.valueThreshold Instance.continuationValue
  rw [harg, hmax, mul_assoc]

/-- A Bellman child retains every identity other than its arriving candidate,
with the increasing `succAbove` enumeration. -/
def Instance.child {n : ℕ} (P : Instance (n + 1)) (i : Fin (n + 1)) : Instance n :=
  P.restrictBy (Fin.succAboveEmb i)

end ProphetSecretary.Model
