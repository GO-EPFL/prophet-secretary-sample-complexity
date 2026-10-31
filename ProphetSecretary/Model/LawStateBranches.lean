import ProphetSecretary.Model.RootAcceptance
import ProphetSecretary.Model.BoundaryBranches
import ProphetSecretary.Analysis.RootActionLoss

/-!
# Actual finite state branches under a law perturbation

The old canonical observer acts on its actual strict-past history. Every child
uses the original unseen identity set, including identities revealed at value
zero. Root quantities use complete vectors only in this analytical decomposition.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

private lemma durationRoot_congr_instance {m : ℕ} {P Q : Instance m} (hPQ : P = Q)
    (hP : Integrable Instance.maximum P.valuesLaw) (hQ : Integrable Instance.maximum Q.valuesLaw) (x : ℝ) :
    P.durationRoot hP x = Q.durationRoot hQ x := by
  cases hPQ
  rfl

noncomputable def Instance.lawStateRoot (P : Instance n) {H : ℝ}
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (w θ : ℝ) (A : Finset (Fin n)) (x : ℝ) : ℝ :=
  w * (P.restrictTo A).lawDurationRoot (fun j ↦ hbound (stateEmbedding A j))
    (fun j ↦ h (stateEmbedding A j)) (fun j ↦ hh (stateEmbedding A j))
    (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) θ x

noncomputable def Instance.lawStateValue (P : Instance n)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (w θ : ℝ) (A : Finset (Fin n)) (d : ℝ) : ℝ :=
  ((P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j))
    (fun j ↦ hm (stateEmbedding A j)) θ).weightedSaturatedValue w d

lemma Instance.lawStateRoot_eq_instanceRoot (P : Instance n) {H : ℝ}
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (w θ : ℝ) (A : Finset (Fin n)) (x : ℝ) :
    P.lawStateRoot hbound h hh hb hm w θ A x =
      w * ((P.likelihoodWidePath h hh hb hm θ).restrictTo A).durationRoot
        ((P.likelihoodWidePath h hh hb hm θ).restrictTo_integrable_maximum A
          ((P.likelihoodWidePath h hh hb hm θ).integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound))) x := by
  apply congrArg (fun d : ℝ ↦ w * d)
  exact (durationRoot_congr_instance (P.likelihoodWidePath_restrictTo h hh hb hm θ A) _ _ x).symm

lemma Instance.lawStateValue_eq_instanceValue (P : Instance n)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (w θ : ℝ) (A : Finset (Fin n)) (d : ℝ) :
    P.lawStateValue h hh hb hm w θ A d =
      optimalScalarValue ((P.likelihoodWidePath h hh hb hm θ).restrictTo A) w (max 0 d) := by
  rw [P.likelihoodWidePath_restrictTo h hh hb hm θ A]
  rfl

lemma Instance.continuationAtArrival_eq_lawStateValue (P : Instance n)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (w θ : ℝ) {c : ℝ} (hc : 0 ≤ c) (x u : Fin n → ℝ) (i : Fin n) (t : ℝ)
    (A : Finset (Fin n)) (hA : otherUnseen u i t = A) :
    (P.likelihoodWidePath h hh hb hm θ).continuationAtArrival w c x (Function.update u i t) i =
      P.lawStateValue h hh hb hm w θ A (c * (1 - t)) := by
  unfold Instance.continuationAtArrival
  rw [Function.update_self, unseen_replaceClock_erase, hA, P.lawStateValue_eq_instanceValue h hh hb hm w θ A]
  change optimalScalarValue _ w (c * max 0 (1 - t)) = optimalScalarValue _ w (max 0 (c * (1 - t)))
  congr 1
  rw [mul_max_of_nonneg _ _ hc, mul_zero]

lemma Instance.lawPolicy_action_iff_stateRoot (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ : ℝ) (x u : Fin n → ℝ) (i : Fin n) {t : ℝ} (ht : t < 1)
    (A : Finset (Fin n)) (hA : otherUnseen u i t = A) :
    let Q := P.likelihoodWidePath h hh hb hm θ
    let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
    ((Q.valuePolicy hQ hw.le hc.le).rule.action () Finset.univ x (Function.update u i t) i = true) ↔
      1 - P.lawStateRoot hbound h hh hb hm w θ A (x i) / c ≤ t := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  have hChild := Q.restrictTo_integrable_maximum A hQ
  let π : Policy Unit n := (Q.valuePolicy hQ hw.le hc.le).rule
  have hAct : (π.action () Finset.univ x (Function.update u i t) i = true) ↔
      Q.continuationAtArrival w c x (Function.update u i t) i ≤ w * x i :=
    Q.valuePolicy_action_iff_continuation hQ hw hc.le x (Function.update u i t) i
  have hv : Q.continuationAtArrival w c x (Function.update u i t) i =
      optimalScalarValue (Q.restrictTo A) w (c * (1 - t)) := by
    unfold Instance.continuationAtArrival
    rw [Function.update_self, unseen_replaceClock_erase, hA, max_eq_right (sub_pos.mpr ht).le]
    rfl
  change (π.action () Finset.univ x (Function.update u i t) i = true) ↔ _
  rw [hAct, hv, (Q.restrictTo A).durationRoot_acceptance_iff hChild hw hc ht,
    P.lawStateRoot_eq_instanceRoot hbound h hh hb hm w θ A (x i)]

lemma Instance.lawPolicy_arrivalLoss_eq_stateBranch (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (x u : Fin n → ℝ) (i : Fin n) {t : ℝ} (ht : t < 1)
    (A : Finset (Fin n)) (hA : otherUnseen u i t = A) :
    let Q := P.likelihoodWidePath h hh hb hm θ
    let T := P.likelihoodWidePath h hh hb hm ρ
    let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
    (Q.valuePolicy hQ hw.le hc.le).rule.arrivalBellmanLoss T w c () x (Function.update u i t) i =
      ProphetSecretary.Analysis.rootActionLoss (P.lawStateValue h hh hb hm w ρ A) (w * x i) c
        (P.lawStateRoot hbound h hh hb hm w θ A (x i)) t := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  let T := P.likelihoodWidePath h hh hb hm ρ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let π : Policy Unit n := (Q.valuePolicy hQ hw.le hc.le).rule
  have hAct : (π.action () Finset.univ x (Function.update u i t) i = true) ↔
      1 - P.lawStateRoot hbound h hh hb hm w θ A (x i) / c ≤ t :=
    P.lawPolicy_action_iff_stateRoot hw hc hbound h hh hb hm θ x u i ht A hA
  have hV := P.continuationAtArrival_eq_lawStateValue h hh hb hm w ρ hc.le x u i t A hA
  change π.arrivalBellmanLoss T w c () x (Function.update u i t) i = _
  unfold Policy.arrivalBellmanLoss ProphetSecretary.Analysis.rootActionLoss
  rw [hV]
  simp only [hAct]

end ProphetSecretary.Model
