import ProphetSecretary.Model.MappedBellmanLoss

/-!
# Premium differences under a value map

The continuation is indexed by the observed unseen set and hence depends on the
clock vector, not on realized offer values. Changing the candidate reward gives
a uniformly bounded max difference whose marginal mean is exactly the negative
cross-law transition residual. Paper correspondence: `upmom:transport`.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.mappedPremiumDifference (Q : Instance n) (f : Fin n → ℝ → ℝ)
    (w c : ℝ) (i : Fin n) (z : (Fin n → ℝ) × ℝ) : ℝ :=
  max (w * z.2) (Q.continuationAtArrival w c (fun _ => 0) z.1 i) -
    max (w * f i z.2) (Q.continuationAtArrival w c (fun _ => 0) z.1 i)

lemma abs_max_mapped_difference_le {a b v h w : ℝ} (hw : 0 ≤ w) (hdispl : |b - a| ≤ h) :
    |max (w * a) v - max (w * b) v| ≤ w * h := by
  have hm := abs_max_sub_max_le_abs (w * a) (w * b) v
  have heq : w * a - w * b = w * (a - b) := by ring
  rw [heq, abs_mul, abs_of_nonneg hw] at hm
  have hδ : |a - b| ≤ h := by simpa only [abs_sub_comm] using hdispl
  exact hm.trans (mul_le_mul_of_nonneg_left hδ hw)

lemma Instance.mappedPremiumDifference_bound (Q : Instance n) (f : Fin n → ℝ → ℝ)
    {h w : ℝ} (hw : 0 ≤ w) (hdispl : ∀ i a, |f i a - a| ≤ h) (c : ℝ)
    (i : Fin n) (u : Fin n → ℝ) (a : ℝ) :
    |Q.mappedPremiumDifference f w c i (u, a)| ≤ w * h :=
  abs_max_mapped_difference_le hw (hdispl i a)

lemma Instance.measurable_mappedPremiumDifference (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (i : Fin n) :
    Measurable (Q.mappedPremiumDifference f w c i) := by
  have hv : Measurable (fun u : Fin n → ℝ => Q.continuationAtArrival w c (fun _ => 0) u i) :=
    Q.measurable_continuationAtArrival hQ hw hc (x := fun _ => fun _ => 0) (u := id)
      (fun _ => measurable_const) (fun j => measurable_pi_apply j) i
  have ha : Measurable (fun z : (Fin n → ℝ) × ℝ => w * z.2) := measurable_const.mul measurable_snd
  have hfa : Measurable (fun z : (Fin n → ℝ) × ℝ => w * f i z.2) :=
    measurable_const.mul ((hf i).comp measurable_snd)
  exact (ha.max (hv.comp measurable_fst)).sub (hfa.max (hv.comp measurable_fst))

/-- The cancellation uses the actual pushed-forward marginal law. The policy
has not been changed or reoptimized by this identity. -/
theorem Instance.integral_mappedPremiumDifference (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h : ℝ} (hdispl : ∀ i a, |f i a - a| ≤ h) (w c : ℝ) (i : Fin n) (u : Fin n → ℝ) :
    (∫ a, (P.mapValues f hf hnn).mappedPremiumDifference f w c i (u, a) ∂P.law i) =
      -(P.mapValues f hf hnn).transitionResidual P w c u i := by
  let Q := P.mapValues f hf hnn
  let v := Q.continuationAtArrival w c (fun _ => 0) u i
  have hδ : ∀ i, ∀ᵐ x ∂P.law i, |f i x - x| ≤ h := fun i => Eventually.of_forall (hdispl i)
  have hIf := P.integrable_valueTransform_of_bounded_displacement hP f hf hδ
  have hQ := P.mapValues_integrable_maximum f hf hnn hIf
  have hPi := (P.integrable_maximum_iff.mp hP) i
  have hleft : Integrable (fun a => max (w * a) v) (P.law i) := integrable_max_with _ hPi w v
  have hright : Integrable (fun a => max (w * f i a) v) (P.law i) :=
    ((hIf i).const_mul w).sup (integrable_const v)
  have hg : Measurable (fun a : ℝ => max (w * a) v) :=
    (measurable_const.mul measurable_id).max measurable_const
  have hmap := integral_map (μ := P.law i) (hf i).aemeasurable hg.aestronglyMeasurable
  change (∫ a, max (w * a) v ∂Q.law i) = ∫ a, max (w * f i a) v ∂P.law i at hmap
  change (∫ a, max (w * a) v - max (w * f i a) v ∂P.law i) = -(Q.lawResidual P i w v)
  rw [integral_sub hleft hright, ← hmap, Q.lawResidual_eq_maxDifference P hQ hP i w v]
  unfold expectedMaxWith
  ring

/-- General-design form: the mapped true law may differ from the law defining
the continuation potential. All original observations remain available. -/
theorem Instance.integral_mappedPremiumDifference_general (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h : ℝ} (hdispl : ∀ i a, |f i a - a| ≤ h) (w c : ℝ) (i : Fin n) (u : Fin n → ℝ) :
    (∫ a, Q.mappedPremiumDifference f w c i (u, a) ∂P.law i) =
      Q.transitionResidual (P.mapValues f hf hnn) w c u i - Q.transitionResidual P w c u i := by
  let T := P.mapValues f hf hnn
  let v := Q.continuationAtArrival w c (fun _ => 0) u i
  have hδ : ∀ i, ∀ᵐ x ∂P.law i, |f i x - x| ≤ h := fun i => Eventually.of_forall (hdispl i)
  have hIf := P.integrable_valueTransform_of_bounded_displacement hP f hf hδ
  have hT := P.mapValues_integrable_maximum f hf hnn hIf
  have hleft : Integrable (fun a => max (w * a) v) (P.law i) :=
    integrable_max_with _ ((P.integrable_maximum_iff.mp hP) i) w v
  have hright : Integrable (fun a => max (w * f i a) v) (P.law i) :=
    ((hIf i).const_mul w).sup (integrable_const v)
  have hg : Measurable (fun a : ℝ => max (w * a) v) :=
    (measurable_const.mul measurable_id).max measurable_const
  have hmap := integral_map (μ := P.law i) (hf i).aemeasurable hg.aestronglyMeasurable
  change (∫ a, max (w * a) v ∂T.law i) = ∫ a, max (w * f i a) v ∂P.law i at hmap
  change (∫ a, max (w * a) v - max (w * f i a) v ∂P.law i) =
    Q.lawResidual T i w v - Q.lawResidual P i w v
  rw [integral_sub hleft hright, ← hmap,
    Q.lawResidual_eq_maxDifference T hQ hT i w v,
    Q.lawResidual_eq_maxDifference P hQ hP i w v]
  unfold expectedMaxWith
  ring

end ProphetSecretary.Model
