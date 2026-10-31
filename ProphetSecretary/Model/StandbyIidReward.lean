import ProphetSecretary.Model.IidRewardRecursion

/-! # A fixed iid marginal with one deterministic standby offer
`μ` is a single fixed law in both recursions. Decreasing the remaining count
does not replace it by a law whose probabilities use that smaller count.
-/
open MeasureTheory
open scoped Classical BigOperators
namespace ProphetSecretary.Model

noncomputable def iidOfferInstance (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (m : ℕ) : Instance m where
  law _ := μ
  probability _ := inferInstance
  nonnegative _ := hμ

noncomputable def standbyIidInstance (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (a : ℝ) (ha : 0 ≤ a) (m : ℕ) : Instance (m + 1) where
  law i := if i = 0 then Measure.dirac a else μ
  probability i := by split_ifs <;> infer_instance
  nonnegative i := by
    split_ifs
    · simpa using ha
    · exact hμ

lemma iidOfferInstance_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hi : Integrable id μ) (m : ℕ) :
    Integrable Instance.maximum (iidOfferInstance μ hμ m).valuesLaw :=
  (iidOfferInstance μ hμ m).integrable_maximum (fun _ ↦ hi)

lemma standbyIidInstance_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hi : Integrable id μ) (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    Integrable Instance.maximum (standbyIidInstance μ hμ a ha m).valuesLaw := by
  apply (standbyIidInstance μ hμ a ha m).integrable_maximum
  intro i
  change Integrable id (if i = 0 then Measure.dirac a else μ)
  split_ifs
  · exact integrable_dirac (by simp)
  · exact hi

@[simp] lemma iidOfferInstance_child (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {m : ℕ} (i : Fin (m + 1)) :
    (iidOfferInstance μ hμ (m + 1)).child i = iidOfferInstance μ hμ m := by
  apply Instance.eq_of_law_eq
  rfl

@[simp] lemma standbyIidInstance_law_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    (standbyIidInstance μ hμ a ha m).law 0 = Measure.dirac a := by simp [standbyIidInstance]

@[simp] lemma standbyIidInstance_law_succ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (a : ℝ) (ha : 0 ≤ a) {m : ℕ} (i : Fin m) :
    (standbyIidInstance μ hμ a ha m).law i.succ = μ := by simp [standbyIidInstance]

@[simp] lemma standbyIidInstance_child_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    (standbyIidInstance μ hμ a ha m).child 0 = iidOfferInstance μ hμ m := by
  apply Instance.eq_of_law_eq
  funext i
  change (if (0 : Fin (m + 1)).succAbove i = 0 then Measure.dirac a else μ) = μ
  simp

@[simp] lemma standbyIidInstance_child_succ (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (a : ℝ) (ha : 0 ≤ a) {m : ℕ} (i : Fin (m + 1)) :
    (standbyIidInstance μ hμ a ha (m + 1)).child i.succ = standbyIidInstance μ hμ a ha m := by
  apply Instance.eq_of_law_eq
  funext j
  change (if i.succ.succAbove j = 0 then Measure.dirac a else μ) =
    (if j = 0 then Measure.dirac a else μ)
  simp only [Fin.succAbove_eq_zero_iff (Fin.succ_ne_zero i)]

noncomputable def marginalMaximum (μ : Measure ℝ) (v : ℝ) : ℝ := ∫ x, max x v ∂μ

noncomputable def iidRewardSequence (μ : Measure ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => marginalMaximum μ (iidRewardSequence μ m)

noncomputable def standbyRewardSequence (μ : Measure ℝ) (a : ℝ) : ℕ → ℝ
  | 0 => a
  | m + 1 => (max a (iidRewardSequence μ (m + 1)) +
      ((m : ℝ) + 1) * marginalMaximum μ (standbyRewardSequence μ a m)) / ((m : ℝ) + 2)

/-- `S_m=f(S_{m-1})`, derived for the full admissible policy class. -/
theorem iidOfferInstance_optimalReward (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hi : Integrable id μ) (m : ℕ) :
    optimalScalarValue (iidOfferInstance μ hμ m) 1 0 = iidRewardSequence μ m := by
  induction m with
  | zero => exact optimalScalarValue_empty _ 1 0
  | succ m ih =>
    rw [(iidOfferInstance μ hμ (m + 1)).optimalReward_bellman (iidOfferInstance_integrable μ hμ hi (m + 1))]
    simp_rw [iidOfferInstance_child, ih]
    change (∑ _i : Fin (m + 1), marginalMaximum μ (iidRewardSequence μ m)) / ((m : ℝ) + 1) = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
      iidRewardSequence]
    field_simp

/-- `W_m=(max(a,S_m)+m f(W_{m-1}))/(m+1)` for the same fixed marginal. -/
theorem standbyIidInstance_optimalReward (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hi : Integrable id μ) (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    optimalScalarValue (standbyIidInstance μ hμ a ha m) 1 0 = standbyRewardSequence μ a m := by
  induction m with
  | zero =>
    let P := standbyIidInstance μ hμ a ha 0
    have hP := standbyIidInstance_integrable μ hμ hi a ha 0
    rw [P.optimalScalarValue_oneOffer hP zero_le_one le_rfl, zero_add,
      integral_prod _ (P.integrable_oneOfferPremium hP 1 0)]
    change (∫ x : ℝ, ∫ t : ℝ, Instance.oneOfferPremium 1 0 (x, t) ∂Instance.uniformClock ∂Measure.dirac a) = a
    simp [Instance.oneOfferPremium, max_eq_right ha]
  | succ m ih =>
    rw [(standbyIidInstance μ hμ a ha (m + 1)).optimalReward_bellman
      (standbyIidInstance_integrable μ hμ hi a ha (m + 1)), Fin.sum_univ_succ]
    simp_rw [standbyIidInstance_child_zero, standbyIidInstance_child_succ,
      iidOfferInstance_optimalReward μ hμ hi, ih, standbyIidInstance_law_zero, standbyIidInstance_law_succ]
    simp only [integral_dirac, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    conv_rhs => rw [standbyRewardSequence]
    congr 1
    ring

end ProphetSecretary.Model
