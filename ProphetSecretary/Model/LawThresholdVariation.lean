import ProphetSecretary.Probability.WidePolicyLikelihood
import ProphetSecretary.Model.BellmanResidual
import ProphetSecretary.Analysis.ThresholdLoss

/-!
# Finite law variation of continuation thresholds

Restriction keeps the original score belonging to every unseen identity. A
common fixed-policy Lipschitz bound then controls every continuation value,
including zero remaining horizon, before actions are compared under a new law.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

lemma Instance.likelihoodWidePath_restrictTo (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1)
    (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) (θ : ℝ) (A : Finset (Fin n)) :
    (P.likelihoodWidePath h hh hb hm θ).restrictTo A =
      (P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
        (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j))
        (fun j ↦ hm (stateEmbedding A j)) θ := by
  rfl

/-- Uniform over the current history and elapsed clock. Finite cardinality is
allowed in this preliminary local law-regret estimate. -/
theorem Instance.continuationAtArrival_likelihoodWidePath_lipschitz (P : Instance n)
    {w c H : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2))
    (x u : Fin n → ℝ) (i : Fin n) (ht : 0 ≤ u i) :
    |(P.likelihoodWidePath h hh hb hm ρ).continuationAtArrival w c x u i -
      (P.likelihoodWidePath h hh hb hm θ).continuationAtArrival w c x u i| ≤
        (2 * (w * H + c) * (n : ℝ)) * |ρ - θ| := by
  let A := (unseen (history Finset.univ x u (u i))).erase i
  let ce := c * max 0 (1 - u i)
  have hce0 : 0 ≤ ce := mul_nonneg hc (le_max_left _ _)
  have hce1 : ce ≤ c := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (max_le zero_le_one (sub_le_self 1 ht)) hc
  have hL := (P.restrictTo A).optimalScalarValue_likelihoodWidePath_lipschitz hw hce0 hH
    (fun j ↦ hbound (stateEmbedding A j)) (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j))
    (fun j ↦ hm (stateEmbedding A j)) hθ hρ
  change |optimalScalarValue ((P.likelihoodWidePath h hh hb hm ρ).restrictTo A) w ce -
    optimalScalarValue ((P.likelihoodWidePath h hh hb hm θ).restrictTo A) w ce| ≤ _
  rw [P.likelihoodWidePath_restrictTo h hh hb hm ρ A, P.likelihoodWidePath_restrictTo h hh hb hm θ A]
  apply hL.trans
  have hCardNat : A.card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ A)
  have hCard : (A.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hCardNat
  have hConst : 2 * (w * H + ce) * (A.card : ℝ) ≤ 2 * (w * H + c) * (n : ℝ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (by linarith : w * H + ce ≤ w * H + c) (by norm_num))
      hCard (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_right hConst (abs_nonneg _)

lemma Instance.valuePolicy_action_iff_continuation (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (x u : Fin n → ℝ) (i : Fin n) :
    ((P.valuePolicy hP hw.le hc).rule.action () Finset.univ x u i = true) ↔
      P.continuationAtArrival w c x u i ≤ w * x i := by
  rw [P.continuationAtArrival_eq_threshold hw]
  change Decidable.decide (_ ≤ _) = true ↔ w * _ ≤ w * _
  rw [decide_eq_true_eq, mul_le_mul_iff_right₀ hw]

/-- The old canonical action can incur loss under the new law only in a band
whose width is the actual finite law-threshold variation. -/
theorem Instance.lawPolicy_localLoss_le_band (P : Instance n)
    {w c H : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2))
    (x u : Fin n → ℝ) (i : Fin n) (ht : 0 ≤ u i) :
    let Q := P.likelihoodWidePath h hh hb hm θ
    let T := P.likelihoodWidePath h hh hb hm ρ
    let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
    let D := (2 * (w * H + c) * (n : ℝ)) * |ρ - θ|
    (Q.valuePolicy hQ hw.le hc).rule.arrivalBellmanLoss T w c () x u i ≤
      if |w * x i - T.continuationAtArrival w c x u i| ≤ D then D else 0 := by
  dsimp only
  let Q := P.likelihoodWidePath h hh hb hm θ
  let T := P.likelihoodWidePath h hh hb hm ρ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let π : Policy Unit n := (Q.valuePolicy hQ hw.le hc).rule
  have hAct : (π.action () Finset.univ x u i = true) ↔ Q.continuationAtArrival w c x u i ≤ w * x i :=
    Q.valuePolicy_action_iff_continuation hQ hw hc x u i
  have hShift := P.continuationAtArrival_likelihoodWidePath_lipschitz hw.le hc hH hbound h hh hb hm hθ hρ x u i ht
  rw [abs_sub_comm] at hShift
  change π.arrivalBellmanLoss T w c () x u i ≤ _
  unfold Policy.arrivalBellmanLoss
  simp only [hAct]
  exact ProphetSecretary.Analysis.max_action_loss_le_band hShift

end ProphetSecretary.Model
