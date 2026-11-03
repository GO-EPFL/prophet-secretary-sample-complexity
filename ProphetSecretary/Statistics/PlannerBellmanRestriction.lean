import ProphetSecretary.Statistics.PlannerBellman
import ProphetSecretary.Model.Reindex

/-!
# The all-arrivals recursion on an observed unseen set

Increasing enumeration transports the finite recursion back to the original
identities. The proof preserves subset sizes and the actual marginal laws.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

private lemma sum_plannerSubsets_map {α β R : Type*} [DecidableEq α] [DecidableEq β]
    [AddCommMonoid R] (e : α ↪ β) (S : Finset α) (f : Finset β → R) :
    (∑ C ∈ (S.map e).powerset, f C) = ∑ B ∈ S.powerset, f (B.map e) := by
  simp only [Finset.map_eq_image, Finset.powerset_image]
  rw [Finset.sum_image]
  exact fun B _ C _ h => Finset.image_injective e.injective h

variable {n : ℕ}

lemma Instance.continuationValue_substate_map (Q : Instance n) (A : Finset (Fin n))
    (B : Finset (Fin A.card)) (hQ : Integrable Instance.maximum Q.valuesLaw)
    {v w c : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (Q.restrictTo A).continuationValue B v w c =
      Q.continuationValue (B.map (stateEmbedding A)) v w c := by
  unfold Instance.continuationValue
  exact Q.optimalScalarValue_restrictTo_map (A.orderEmbOfFin rfl) B hQ hw (mul_nonneg hc hv)

/-- `alg:all-arrivals` on every original unseen identity set. -/
theorem Instance.continuationValue_allArrivals (Q : Instance n) (A : Finset (Fin n))
    (hQ : Integrable Instance.maximum Q.valuesLaw) {u z : ℝ} (hu : 0 ≤ u) (hz : 0 ≤ z) :
    Q.continuationValue A u 1 z = z*u + ∑ i ∈ A,
      ∫ s, (∑ B ∈ (A.erase i).powerset,
        s^B.card * (1-s)^((A.erase i).card-B.card) *
          positivePremium (Q.law i) 1 (Q.continuationValue B (u*s) 1 z)) ∂Instance.uniformClock := by
  let e := stateEmbedding A
  have he : (Finset.univ : Finset (Fin A.card)).map e = A := A.map_orderEmbOfFin_univ rfl
  have hsum (f : Fin n → ℝ) : (∑ j : Fin A.card, f (e j)) = ∑ i ∈ A, f i := by
    have h := Finset.sum_map (Finset.univ : Finset (Fin A.card)) e f
    rw [he] at h
    exact h.symm
  have hcore := (Q.restrictTo A).scalarValue_allArrivals_horizon
    (Q.restrictTo_integrable_maximum A hQ) hu hz
  change Q.continuationValue A u 1 z = _ at hcore
  rw [hcore]
  rw [← hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hErase : (Finset.univ.erase j).map e = A.erase (e j) := by
    rw [Finset.map_erase, he]
  apply integral_congr_ae
  have hsupp : ∀ᵐ s ∂Instance.uniformClock, s ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
  filter_upwards [hsupp] with s hs
  rw [← hErase, sum_plannerSubsets_map]
  apply Finset.sum_congr rfl
  intro B _
  simp only [Finset.card_map]
  have hv := Q.continuationValue_substate_map A B hQ (mul_nonneg hu hs.1) zero_le_one hz
  rw [hv]
  rfl

end ProphetSecretary.Model
