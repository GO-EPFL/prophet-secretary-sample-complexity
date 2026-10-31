import ProphetSecretary.Model.ValueTransform
import ProphetSecretary.Model.LawOrder

/-!
# Dimension-independent value transport

Shifting all values by h changes the scalar optimum by at most wh. Stop-loss
comparison then gives the same bound for any measurable coordinate maps with
uniform displacement at most h, including noninjective maps. Policy pullback
and law order are applied in their proved directions. This supplies the
continuation comparison in `upmom:transport`.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma stopLoss_map (μ : Measure ℝ) (f : ℝ → ℝ) (hf : Measurable f) (b : ℝ) :
    stopLoss (μ.map f) b = ∫ x, max 0 (f x - b) ∂μ :=
  integral_map hf.aemeasurable
    (measurable_const.max (measurable_id.sub measurable_const)).aestronglyMeasurable

lemma stopLoss_map_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hIf : Integrable f μ) (hIg : Integrable g μ)
    (hfg : ∀ᵐ x ∂μ, f x ≤ g x) (b : ℝ) : stopLoss (μ.map f) b ≤ stopLoss (μ.map g) b := by
  rw [stopLoss_map μ f hf b, stopLoss_map μ g hg b]
  exact integral_mono_ae ((integrable_const 0).sup (hIf.sub (integrable_const b)))
    ((integrable_const 0).sup (hIg.sub (integrable_const b)))
    (hfg.mono fun x hx => max_le_max le_rfl (sub_le_sub_right hx b))

noncomputable def Instance.shiftValues (P : Instance n) (h : ℝ) (hh : 0 ≤ h) : Instance n :=
  P.mapValues (fun _ x => x + h) (fun _ => measurable_id.add measurable_const)
    (fun i => (P.nonnegative i).mono fun _ hx => add_nonneg hx hh)

lemma Instance.shiftValues_integrable (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (h : ℝ) (hh : 0 ≤ h) :
    Integrable Instance.maximum (P.shiftValues h hh).valuesLaw :=
  P.mapValues_integrable_maximum _ _ _
    (fun i => ((P.integrable_maximum_iff.mp hP) i).add (integrable_const h))

/-- Any policy on shifted offers pulls back causally to the base offers. Its
reward increases by at most h and its stopping time is exactly preserved. -/
theorem Instance.optimalScalarValue_shiftValues_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {h w c : ℝ}
    (hh : 0 ≤ h) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue (P.shiftValues h hh) w c ≤ optimalScalarValue P w c + w * h := by
  let f : Fin n → ℝ → ℝ := fun _ x => x + h
  have hf : ∀ i, Measurable (f i) := fun _ => measurable_id.add measurable_const
  have hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x :=
    fun i => (P.nonnegative i).mono fun x hx => add_nonneg hx hh
  have hdispl : ∀ i, ∀ᵐ x ∂P.law i, |f i x - x| ≤ h := fun _ =>
    Eventually.of_forall fun x => by dsimp [f]; simp only [add_sub_cancel_left, abs_of_nonneg hh, le_refl]
  change optimalScalarValue (P.mapValues f hf hnn) w c ≤ _
  apply csSup_le (scalarValues_nonempty _ w c)
  rintro z ⟨π, rfl⟩
  have hπ := π.scalarObjective_mapValues_le P hP f hf hnn hh hw c hdispl
  exact hπ.trans (add_le_add (scalarObjective_le_optimal (π.pullbackValuesIndexed f hf) P hP hw hc) le_rfl)

lemma Instance.mapValues_stopLossLE_shift (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h : ℝ} (hh : 0 ≤ h) (hdispl : ∀ i, ∀ᵐ x ∂P.law i, |f i x - x| ≤ h) :
    (P.mapValues f hf hnn).StopLossLE (P.shiftValues h hh) := by
  have hIf := P.integrable_valueTransform_of_bounded_displacement hP f hf hdispl
  intro i b
  change stopLoss ((P.law i).map (f i)) b ≤ stopLoss ((P.law i).map (fun x => x + h)) b
  exact stopLoss_map_le _ _ _ (hf i) (measurable_id.add measurable_const) (hIf i)
    (((P.integrable_maximum_iff.mp hP) i).add (integrable_const h))
    ((hdispl i).mono fun x hx => by
      change f i x ≤ x + h
      linarith only [(abs_le.mp hx).2]) b

lemma Instance.stopLossLE_shift_mapValues (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h : ℝ} (hh : 0 ≤ h) (hdispl : ∀ i, ∀ᵐ x ∂P.law i, |f i x - x| ≤ h) :
    P.StopLossLE ((P.mapValues f hf hnn).shiftValues h hh) := by
  have hIf := P.integrable_valueTransform_of_bounded_displacement hP f hf hdispl
  intro i b
  have hshift : Measurable (fun x : ℝ => x + h) := measurable_id.add measurable_const
  change stopLoss (P.law i) b ≤ stopLoss (((P.law i).map (f i)).map (fun x => x + h)) b
  rw [Measure.map_map hshift (hf i)]
  have hcomp : Measurable (fun x => f i x + h) := (hf i).add measurable_const
  have h := stopLoss_map_le (P.law i) id (fun x => f i x + h) measurable_id hcomp
    ((P.integrable_maximum_iff.mp hP) i) ((hIf i).add (integrable_const h))
    ((hdispl i).mono fun x hx => by
      change x ≤ f i x + h
      linarith only [(abs_le.mp hx).1]) b
  simpa only [Measure.map_id, Function.comp_def] using h

/-- Uniform continuation-value comparison for bounded deterministic value
perturbations. The constant w*h is independent of the number of variables. -/
theorem Instance.optimalScalarValue_mapValues_lipschitz (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h w c : ℝ} (hh : 0 ≤ h) (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hdispl : ∀ i, ∀ᵐ x ∂P.law i, |f i x - x| ≤ h) :
    |optimalScalarValue (P.mapValues f hf hnn) w c - optimalScalarValue P w c| ≤ w * h := by
  let Q := P.mapValues f hf hnn
  have hQ := P.mapValues_integrable_of_bounded_displacement hP f hf hnn hdispl
  have hupper := (Q.optimalScalarValue_mono_stopLoss_nonnegative (P.shiftValues h hh)
    hQ (P.shiftValues_integrable hP h hh) (P.mapValues_stopLossLE_shift hP f hf hnn hh hdispl) hw hc).trans
    (P.optimalScalarValue_shiftValues_le hP hh hw hc)
  have hlower := (P.optimalScalarValue_mono_stopLoss_nonnegative (Q.shiftValues h hh)
    hP (Q.shiftValues_integrable hQ h hh) (P.stopLossLE_shift_mapValues hP f hf hnn hh hdispl) hw hc).trans
    (Q.optimalScalarValue_shiftValues_le hQ hh hw hc)
  rw [abs_le]
  constructor
  · nlinarith only [hlower]
  · nlinarith only [hupper]

end ProphetSecretary.Model
