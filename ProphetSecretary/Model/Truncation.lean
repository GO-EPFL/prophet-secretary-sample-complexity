import ProphetSecretary.Model.Scaling
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Capping and reconstructing finite independent instances

A nonnegative cap parameter includes bounded zero-mean auxiliary instances. Tail limits
in this file keep the finite instance fixed; no estimate uniform in the instance size is
inferred from dominated convergence. Full-information inverse simulation reconstructs
only values whose identities have arrived.
-/

open MeasureTheory Set ProbabilityTheory Filter
open scoped Classical BigOperators Topology ENNReal NNReal

namespace ProphetSecretary.Model

noncomputable def capValue (H : ℝ≥0) (x : ℝ) : ℝ := min x (H : ℝ)

lemma measurable_capValue (H : ℝ≥0) : Measurable (capValue H) :=
  measurable_id.min measurable_const

noncomputable def tailValue (H : ℝ≥0) (x : ℝ) : ℝ := max (x - (H : ℝ)) 0

lemma measurable_tailValue (H : ℝ≥0) : Measurable (tailValue H) :=
  (measurable_id.sub measurable_const).max measurable_const

lemma tailValue_nonnegative (H : ℝ≥0) (x : ℝ) : 0 ≤ tailValue H x := le_max_right _ _

lemma tailValue_le_abs (H : ℝ≥0) (x : ℝ) : tailValue H x ≤ |x| := by
  apply max_le _ (abs_nonneg _)
  exact (sub_le_self x H.property).trans (le_abs_self x)

lemma integrable_tailValue (μ : Measure ℝ) (hμ : Integrable id μ) (H : ℝ≥0) :
    Integrable (tailValue H) μ := by
  apply hμ.abs.mono' (measurable_tailValue H).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (tailValue_nonnegative H x)] using tailValue_le_abs H x

/-- Actual dominated convergence of marginal tail expectations. -/
lemma integral_tailValue_tendsto_zero (μ : Measure ℝ) (hμ : Integrable id μ) :
    Tendsto (fun H : ℝ≥0 => ∫ x, tailValue H x ∂μ) atTop (𝓝 0) := by
  have hlim : ∀ x : ℝ, Tendsto (fun H : ℝ≥0 => tailValue H x) atTop (𝓝 (0 : ℝ)) := by
    intro x
    have he : (fun H : ℝ≥0 => tailValue H x) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_ge_atTop (Real.toNNReal x)] with H hH
      have hxH : x ≤ (H : ℝ) := (Real.le_coe_toNNReal x).trans hH
      exact max_eq_right (sub_nonpos.mpr hxH)
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (fun x : ℝ => |x|)
    (Eventually.of_forall fun H : ℝ≥0 => (measurable_tailValue H).aestronglyMeasurable)
    (Eventually.of_forall fun H : ℝ≥0 => Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (tailValue_nonnegative H x)] using tailValue_le_abs H x)
    hμ.abs (Eventually.of_forall hlim)
  simpa using h

noncomputable def mapHistoryValuesBy {n : ℕ} (g : Fin n → ℝ → ℝ) (h : History n) : History n :=
  fun i => mapObservationValues (g i) (h i)

/-- A value transformation may depend on the independent seed and on the observed
identity. The original policy sees only the transformed current and past observations. -/
noncomputable def Policy.pullbackValuesBy {Seed NewSeed : Type*} {n : ℕ}
    (π : Policy Seed n) (s : NewSeed → Seed) (g : NewSeed → Fin n → ℝ → ℝ) : Policy NewSeed n where
  decide r t i v h := π.decide (s r) t i (g r i v) (mapHistoryValuesBy (g r) h)

section IndexedPullback

variable {Seed NewSeed : Type*} {n : ℕ}

lemma mapHistoryValuesBy_history (g : Fin n → ℝ → ℝ) (D : Finset (Fin n))
    (x u : Fin n → ℝ) (t : ℝ) :
    mapHistoryValuesBy g (history D x u t) = history D (fun i => g i (x i)) u t := by
  funext i
  by_cases hi : i ∈ D ∧ u i < t
  · simp [mapHistoryValuesBy, mapObservationValues, history, hi]
  · simp [mapHistoryValuesBy, mapObservationValues, history, hi]

lemma Policy.pullbackValuesBy_action (π : Policy Seed n) (s : NewSeed → Seed)
    (g : NewSeed → Fin n → ℝ → ℝ) (r : NewSeed) (D : Finset (Fin n))
    (x u : Fin n → ℝ) (i : Fin n) :
    (π.pullbackValuesBy s g).action r D x u i = π.action (s r) D (fun i => g r i (x i)) u i := by
  simp only [Policy.action, Policy.pullbackValuesBy, mapHistoryValuesBy_history]

lemma Policy.pullbackValuesBy_accepted (π : Policy Seed n) (s : NewSeed → Seed)
    (g : NewSeed → Fin n → ℝ → ℝ) (r : NewSeed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    (π.pullbackValuesBy s g).accepted r D x u = π.accepted (s r) D (fun i => g r i (x i)) u := by
  ext i
  simp only [Policy.mem_accepted, Policy.pullbackValuesBy_action]

lemma Policy.pullbackValuesBy_stoppingTime (π : Policy Seed n) (s : NewSeed → Seed)
    (g : NewSeed → Fin n → ℝ → ℝ) (r : NewSeed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    (π.pullbackValuesBy s g).stoppingTime r D x u =
      π.stoppingTime (s r) D (fun i => g r i (x i)) u := by
  unfold Policy.stoppingTime Policy.stopTimes
  simp only [Policy.pullbackValuesBy_accepted]

lemma Policy.pullbackValuesBy_actualSelects_iff (π : Policy Seed n) (s : NewSeed → Seed)
    (g : NewSeed → Fin n → ℝ → ℝ) (r : NewSeed) (D : Finset (Fin n))
    (x u : Fin n → ℝ) (i : Fin n) :
    (π.pullbackValuesBy s g).ActualSelects r D x u i ↔
      π.ActualSelects (s r) D (fun i => g r i (x i)) u i := by
  simp only [Policy.ActualSelects, Policy.Selects, Policy.pullbackValuesBy_accepted,
    Policy.pullbackValuesBy_stoppingTime]

lemma Policy.pullbackValuesBy_reward_loss_le (π : Policy Seed n) (s : NewSeed → Seed)
    (g : NewSeed → Fin n → ℝ → ℝ) (r : NewSeed) (D : Finset (Fin n))
    (x u d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (hgd : ∀ i, g r i (x i) - x i ≤ d i) :
    π.reward (s r) D (fun i => g r i (x i)) u - (π.pullbackValuesBy s g).reward r D x u ≤ ∑ i, d i := by
  unfold Policy.reward
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : (π.pullbackValuesBy s g).ActualSelects r D x u i
  · have hgi := (π.pullbackValuesBy_actualSelects_iff s g r D x u i).mp hi
    simpa only [if_pos hi, if_pos hgi] using hgd i
  · have hgi : ¬π.ActualSelects (s r) D (fun i => g r i (x i)) u i :=
      fun h => hi ((π.pullbackValuesBy_actualSelects_iff s g r D x u i).mpr h)
    simpa only [if_neg hi, if_neg hgi, sub_zero] using hd i

end IndexedPullback

private def observationCode : Option (ℝ × ℝ) → Unit ⊕ (ℝ × ℝ)
  | none => Sum.inl ()
  | some p => Sum.inr p

private lemma measurable_observationCode : Measurable observationCode :=
  Measurable.of_comap_le le_rfl

private def observedTime : Option (ℝ × ℝ) → ℝ
  | none => 0
  | some p => p.1

private def observedValue : Option (ℝ × ℝ) → ℝ
  | none => 0
  | some p => p.2

private lemma measurable_observedTime : Measurable observedTime := by
  have h : Measurable (fun o => Sum.elim (fun _ : Unit => (0 : ℝ)) Prod.fst (observationCode o)) :=
    ((measurable_const : Measurable fun _ : Unit => (0 : ℝ)).sumElim measurable_fst).comp measurable_observationCode
  convert h using 1
  funext o
  cases o <;> rfl

private lemma measurable_observedValue : Measurable observedValue := by
  have h : Measurable (fun o => Sum.elim (fun _ : Unit => (0 : ℝ)) Prod.snd (observationCode o)) :=
    ((measurable_const : Measurable fun _ : Unit => (0 : ℝ)).sumElim measurable_snd).comp measurable_observationCode
  convert h using 1
  funext o
  cases o <;> rfl

private lemma mapObservationValues_eq (g : ℝ → ℝ) (o : Option (ℝ × ℝ)) :
    mapObservationValues g o = if o = none then none else some (observedTime o, g (observedValue o)) := by
  cases o <;> simp [mapObservationValues, observedTime, observedValue]

lemma measurable_mapObservationValuesBy {Ω NewSeed : Type*} [MeasurableSpace Ω]
    [MeasurableSpace NewSeed] {g : NewSeed → ℝ → ℝ}
    (hg : Measurable fun p : NewSeed × ℝ => g p.1 p.2)
    {r : Ω → NewSeed} {o : Ω → Option (ℝ × ℝ)} (hr : Measurable r) (ho : Measurable o) :
    Measurable fun ω => mapObservationValues (g (r ω)) (o ω) := by
  have hn : MeasurableSet {ω | o ω = none} := by
    have hs : MeasurableSet (Set.range (Sum.inl : Unit → Unit ⊕ (ℝ × ℝ))) := measurableSet_range_inl
    have h := hs.preimage (measurable_observationCode.comp ho)
    convert h using 1
    ext ω
    cases hω : o ω <;> simp [observationCode, hω]
  have hs : Measurable (fun ω => some (observedTime (o ω), g (r ω) (observedValue (o ω)))) := by
    rw [measurable_comap_iff]
    exact measurable_inr.comp ((measurable_observedTime.comp ho).prodMk
      (hg.comp (hr.prodMk (measurable_observedValue.comp ho))))
  convert Measurable.ite hn (measurable_const : Measurable fun _ : Ω => (none : Option (ℝ × ℝ))) hs using 1
  funext ω
  exact mapObservationValues_eq _ _

lemma Policy.pullbackValuesBy_isMeasurable {Seed NewSeed : Type*} [MeasurableSpace Seed]
    [MeasurableSpace NewSeed] {n : ℕ} (π : Policy Seed n) (hπ : π.IsMeasurable)
    (s : NewSeed → Seed) (hs : Measurable s) (g : NewSeed → Fin n → ℝ → ℝ)
    (hg : ∀ i, Measurable fun p : NewSeed × ℝ => g p.1 i p.2) :
    (π.pullbackValuesBy s g).IsMeasurable := by
  let W := NewSeed × (ℝ × (Fin n × (ℝ × History n)))
  have hr : Measurable (fun w : W => w.1) := measurable_fst
  have ht : Measurable (fun w : W => w.2.1) := measurable_snd.fst
  have hi : Measurable (fun w : W => w.2.2.1) := measurable_snd.snd.fst
  have hv : Measurable (fun w : W => w.2.2.2.1) := measurable_snd.snd.snd.fst
  have hval : Measurable (fun w : W => g w.1 w.2.2.1 w.2.2.2.1) := by
    have hm : Measurable (fun p : (NewSeed × ℝ) × Fin n => g p.1.1 p.2 p.1.2) :=
      measurable_from_prod_countable_left fun i => hg i
    exact hm.comp ((hr.prodMk hv).prodMk hi)
  have hh : Measurable (fun w : W => mapHistoryValuesBy (g w.1) w.2.2.2.2) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_mapObservationValuesBy (g := fun r v => g r i v) (hg i) hr
      ((measurable_pi_apply i).comp measurable_snd.snd.snd.snd)
  exact hπ.comp ((hs.comp hr).prodMk (ht.prodMk (hi.prodMk (hval.prodMk hh))))

lemma Policy.reward_cap_le_pullback {Seed : Type*} {n : ℕ} (π : Policy Seed n) (H : ℝ≥0)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    π.reward r D (capValue H ∘ x) u ≤ (π.pullbackValues (capValue H)).reward r D x u := by
  unfold Policy.reward
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : (π.pullbackValues (capValue H)).ActualSelects r D x u i
  · have hgi := (π.pullbackValues_actualSelects_iff (capValue H) r D x u i).mp hi
    simp only [if_pos hi, if_pos hgi, Function.comp_apply]
    exact min_le_left _ _
  · have hgi : ¬π.ActualSelects r D (capValue H ∘ x) u i :=
      fun h => hi ((π.pullbackValues_actualSelects_iff (capValue H) r D x u i).mpr h)
    simp only [if_neg hi, if_neg hgi, le_refl]

lemma sub_capValue_eq_tailValue (H : ℝ≥0) (x : ℝ) : x - capValue H x = tailValue H x := by
  by_cases h : x ≤ (H : ℝ)
  · simp [capValue, tailValue, min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
  · have hx : (H : ℝ) ≤ x := (lt_of_not_ge h).le
    simp [capValue, tailValue, min_eq_right hx, max_eq_left (sub_nonneg.mpr hx)]

namespace Truncation

/-- A genuine probability law even when the original tail has zero probability. -/
noncomputable def tailLaw (μ : Measure ℝ) (H : ℝ≥0) : Measure ℝ :=
  if μ (Ici (H : ℝ)) = 0 then Measure.dirac (H : ℝ) else ProbabilityTheory.cond μ (Ici (H : ℝ))

instance tailLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (H : ℝ≥0) :
    IsProbabilityMeasure (tailLaw μ H) := by
  by_cases h : μ (Ici (H : ℝ)) = 0
  · simpa only [tailLaw, if_pos h] using (inferInstance : IsProbabilityMeasure (Measure.dirac (H : ℝ)))
  · simpa only [tailLaw, if_neg h] using cond_isProbabilityMeasure h

lemma tailLaw_mem (μ : Measure ℝ) [IsProbabilityMeasure μ] (H : ℝ≥0) :
    ∀ᵐ x ∂tailLaw μ H, (H : ℝ) ≤ x := by
  by_cases h : μ (Ici (H : ℝ)) = 0
  · simp [tailLaw, h]
  · simpa only [tailLaw, if_neg h, mem_Ici] using (ae_cond_mem (μ := μ) (s := Ici (H : ℝ)) measurableSet_Ici)

lemma smul_tailLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (H : ℝ≥0) :
    μ (Ici (H : ℝ)) • tailLaw μ H = μ.restrict (Ici (H : ℝ)) := by
  by_cases h : μ (Ici (H : ℝ)) = 0
  · rw [h, zero_smul, Measure.restrict_eq_zero.mpr h]
  · simp only [tailLaw, if_neg h, ProbabilityTheory.cond, smul_smul]
    rw [ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_smul]

noncomputable def reconstruct (H : ℝ≥0) (p : ℝ × ℝ) : ℝ :=
  if p.1 < (H : ℝ) then p.1 else p.2

lemma measurable_reconstruct (H : ℝ≥0) : Measurable (reconstruct H) :=
  Measurable.ite (measurableSet_lt measurable_fst measurable_const) measurable_fst measurable_snd

lemma reconstruct_cap (H : ℝ≥0) (p : ℝ × ℝ) :
    reconstruct H (capValue H p.1, p.2) = reconstruct H p := by
  by_cases h : p.1 < (H : ℝ)
  · simp [reconstruct, capValue, min_eq_left h.le, h]
  · simp [reconstruct, capValue, min_eq_right (le_of_not_gt h), h]

/-- Replacing the tail of an original draw by an independent conditional tail draw
preserves its law exactly. -/
lemma reconstruct_original_map (μ : Measure ℝ) [IsProbabilityMeasure μ] (H : ℝ≥0) :
    (μ.prod (tailLaw μ H)).map (reconstruct H) = μ := by
  let A := μ.restrict (Iio (H : ℝ))
  let B := μ.restrict (Ici (H : ℝ))
  have hAB : A + B = μ := by
    simpa only [A, B, compl_Iio] using
      (Measure.restrict_add_restrict_compl (μ := μ) (s := Iio (H : ℝ)) measurableSet_Iio)
  have hA : (A.prod (tailLaw μ H)).map (reconstruct H) = A := by
    have hm : ∀ᵐ p ∂A.prod (tailLaw μ H), p.1 < (H : ℝ) :=
      (measurePreserving_fst (μ := A) (ν := tailLaw μ H)).quasiMeasurePreserving.ae
        (ae_restrict_mem measurableSet_Iio)
    calc
      _ = (A.prod (tailLaw μ H)).map Prod.fst := Measure.map_congr (hm.mono fun p hp => if_pos hp)
      _ = A := (measurePreserving_fst (μ := A) (ν := tailLaw μ H)).map_eq
  have hB : (B.prod (tailLaw μ H)).map (reconstruct H) = B := by
    have hm : ∀ᵐ p ∂B.prod (tailLaw μ H), (H : ℝ) ≤ p.1 :=
      (measurePreserving_fst (μ := B) (ν := tailLaw μ H)).quasiMeasurePreserving.ae
        (ae_restrict_mem measurableSet_Ici)
    calc
      _ = (B.prod (tailLaw μ H)).map Prod.snd :=
        Measure.map_congr (hm.mono fun p hp => if_neg (not_lt_of_ge hp))
      _ = μ (Ici (H : ℝ)) • tailLaw μ H := by simp [B]
      _ = B := smul_tailLaw μ H
  calc
    _ = ((A + B).prod (tailLaw μ H)).map (reconstruct H) := by rw [hAB]
    _ = (A.prod (tailLaw μ H)).map (reconstruct H) +
        (B.prod (tailLaw μ H)).map (reconstruct H) := by
      rw [Measure.add_prod, Measure.map_add _ _ (measurable_reconstruct H)]
    _ = A + B := by rw [hA, hB]
    _ = μ := hAB

/-- The explicit inverse randomization reconstructs the true law from a capped draw. -/
lemma reconstruct_measurePreserving (μ : Measure ℝ) [IsProbabilityMeasure μ] (H : ℝ≥0) :
    MeasurePreserving (reconstruct H) ((μ.map (capValue H)).prod (tailLaw μ H)) μ := by
  have hcap : MeasurePreserving (fun p : ℝ × ℝ => (capValue H p.1, p.2))
      (μ.prod (tailLaw μ H)) ((μ.map (capValue H)).prod (tailLaw μ H)) :=
    (show MeasurePreserving (capValue H) μ (μ.map (capValue H)) from ⟨measurable_capValue H, rfl⟩).prod
      (MeasurePreserving.id _)
  refine ⟨measurable_reconstruct H, ?_⟩
  rw [← hcap.map_eq, Measure.map_map (measurable_reconstruct H) hcap.measurable]
  have he : (reconstruct H ∘ (fun p : ℝ × ℝ => (capValue H p.1, p.2))) = reconstruct H :=
    funext (reconstruct_cap H)
  rw [he]
  exact reconstruct_original_map μ H

lemma cap_reconstruct_ae (μ : Measure ℝ) [IsProbabilityMeasure μ] (H : ℝ≥0) :
    ∀ᵐ p ∂(μ.map (capValue H)).prod (tailLaw μ H), capValue H (reconstruct H p) = p.1 := by
  letI := Measure.isProbabilityMeasure_map (μ := μ) (measurable_capValue H).aemeasurable
  have hy : ∀ᵐ y ∂μ.map (capValue H), y ≤ (H : ℝ) := by
    apply (ae_map_iff (measurable_capValue H).aemeasurable measurableSet_Iic).mpr
    exact Eventually.of_forall fun x => min_le_right _ _
  have hy' := (measurePreserving_fst (μ := μ.map (capValue H)) (ν := tailLaw μ H)).quasiMeasurePreserving.ae hy
  have hz := (measurePreserving_snd (μ := μ.map (capValue H)) (ν := tailLaw μ H)).quasiMeasurePreserving.ae
    (tailLaw_mem μ H)
  filter_upwards [hy', hz] with p hp hz
  by_cases h : p.1 < (H : ℝ)
  · simp [reconstruct, capValue, h, min_eq_left h.le]
  · have he : p.1 = (H : ℝ) := le_antisymm hp (le_of_not_gt h)
    simp [reconstruct, capValue, he, min_eq_right hz]

end Truncation

namespace Instance

variable {n : ℕ}

noncomputable def cap (P : Instance n) (H : ℝ≥0) : Instance n where
  law i := (P.law i).map (capValue H)
  probability i := Measure.isProbabilityMeasure_map (measurable_capValue H).aemeasurable
  nonnegative i := by
    apply (ae_map_iff (measurable_capValue H).aemeasurable measurableSet_Ici).mpr
    exact (P.nonnegative i).mono fun _ hx => le_min hx H.property

lemma cap_bounded (P : Instance n) (H : ℝ≥0) (i : Fin n) :
    ∀ᵐ x ∂(P.cap H).law i, x ≤ (H : ℝ) := by
  apply (ae_map_iff (measurable_capValue H).aemeasurable measurableSet_Iic).mpr
  exact Eventually.of_forall fun x => min_le_right _ _

lemma capValues_measurePreserving (P : Instance n) (H : ℝ≥0) :
    MeasurePreserving (fun x : Fin n → ℝ => capValue H ∘ x) P.valuesLaw (P.cap H).valuesLaw := by
  refine ⟨measurable_pi_lambda _ (fun i => (measurable_capValue H).comp (measurable_pi_apply i)), ?_⟩
  exact Measure.pi_map_pi (fun _ => (measurable_capValue H).aemeasurable)

lemma maximum_cap (H : ℝ≥0) (x : Fin n → ℝ) :
    maximum (capValue H ∘ x) = min (maximum x) (H : ℝ) := by
  unfold maximum
  have h := (Finset.sup'_inf_distrib_right ⟨none, Finset.mem_univ _⟩
    (fun j : Option (Fin n) => j.elim 0 x) (H : ℝ)).symm
  convert h using 1
  congr 1
  funext j
  cases j <;> simp [capValue]

lemma cap_integrable_maximum (P : Instance n) (H : ℝ≥0)
    (hP : Integrable maximum P.valuesLaw) : Integrable maximum (P.cap H).valuesLaw := by
  apply ((P.capValues_measurePreserving H).integrable_comp measurable_maximum.aestronglyMeasurable).mp
  have hi : Integrable (fun x => min (maximum x) (H : ℝ)) P.valuesLaw := hP.inf (integrable_const _)
  change Integrable (fun x => maximum (capValue H ∘ x)) P.valuesLaw
  simpa only [maximum_cap] using hi

lemma cap_expectedMaximum (P : Instance n) (H : ℝ≥0) :
    (P.cap H).expectedMaximum = ∫ x, min (maximum x) (H : ℝ) ∂P.valuesLaw := by
  have h := integral_map (μ := P.valuesLaw) (P.capValues_measurePreserving H).measurable.aemeasurable
    measurable_maximum.aestronglyMeasurable
  rw [(P.capValues_measurePreserving H).map_eq] at h
  simpa only [expectedMaximum, maximum_cap] using h

lemma cap_expectedMaximum_le (P : Instance n) (H : ℝ≥0)
    (hP : Integrable maximum P.valuesLaw) : (P.cap H).expectedMaximum ≤ P.expectedMaximum := by
  rw [cap_expectedMaximum]
  exact integral_mono (hP.inf (integrable_const _)) hP (fun _ => min_le_left _ _)

/-- Fixed-finite-instance convergence of the capped expected maximum. -/
lemma cap_expectedMaximum_tendsto (P : Instance n) (hP : Integrable maximum P.valuesLaw) :
    Tendsto (fun H : ℝ≥0 => (P.cap H).expectedMaximum) atTop (𝓝 P.expectedMaximum) := by
  simp only [cap_expectedMaximum]
  apply tendsto_integral_filter_of_dominated_convergence (fun x => maximum x)
  · exact Eventually.of_forall fun H => (measurable_maximum.min measurable_const).aestronglyMeasurable
  · exact Eventually.of_forall fun H => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(neg_nonpos.mpr (maximum_nonnegative x)).trans
        (le_min (maximum_nonnegative x) H.property), min_le_left _ _⟩
  · exact hP
  · apply Eventually.of_forall
    intro x
    have he : (fun H : ℝ≥0 => min (maximum x) (H : ℝ)) =ᶠ[atTop] (fun _ => maximum x) := by
      filter_upwards [eventually_ge_atTop (Real.toNNReal (maximum x))] with H hH
      have hxH : maximum x ≤ (H : ℝ) := (Real.le_coe_toNNReal _).trans hH
      exact min_eq_left hxH
    exact (tendsto_congr' he).mpr tendsto_const_nhds

noncomputable def tailSum (P : Instance n) (H : ℝ≥0) : ℝ :=
  ∑ i, ∫ x, tailValue H x ∂P.law i

lemma tailSum_nonnegative (P : Instance n) (H : ℝ≥0) : 0 ≤ P.tailSum H :=
  Finset.sum_nonneg fun _ _ => integral_nonneg (tailValue_nonnegative H)

/-- The tail sum vanishes with fixed `n`; this makes no assertion uniform in `n`. -/
lemma tailSum_tendsto_zero (P : Instance n) (hP : Integrable maximum P.valuesLaw) :
    Tendsto P.tailSum atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    integral_tailValue_tendsto_zero (P.law i) (P.integrable_maximum_iff.mp hP i))
  change Tendsto (fun H : ℝ≥0 => ∑ i, ∫ x, tailValue H x ∂P.law i) atTop (𝓝 0)
  simpa only [Finset.sum_const_zero] using h

/-- Independent conditional-tail draws, used only as auxiliary policy randomness. -/
noncomputable def tailDrawLaw (P : Instance n) (H : ℝ≥0) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => Truncation.tailLaw (P.law i) H)

instance tailDrawLaw_probability (P : Instance n) (H : ℝ≥0) : IsProbabilityMeasure (P.tailDrawLaw H) := by
  dsimp [tailDrawLaw]
  infer_instance

noncomputable def reconstructedValues (H : ℝ≥0) (p : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℝ :=
  fun i => Truncation.reconstruct H (p.1 i, p.2 i)

/-- The reconstruction yields the complete original independent product law. -/
lemma reconstructedValues_measurePreserving (P : Instance n) (H : ℝ≥0) :
    MeasurePreserving (reconstructedValues H) ((P.cap H).valuesLaw.prod (P.tailDrawLaw H)) P.valuesLaw := by
  have hpair := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) (P.cap H).law
    (fun i => Truncation.tailLaw (P.law i) H)).symm (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
  have hpi := measurePreserving_pi (fun i => ((P.cap H).law i).prod (Truncation.tailLaw (P.law i) H))
    P.law (fun i => Truncation.reconstruct_measurePreserving (P.law i) H)
  exact hpi.comp hpair

lemma cap_reconstructedValues_ae (P : Instance n) (H : ℝ≥0) :
    ∀ᵐ p ∂(P.cap H).valuesLaw.prod (P.tailDrawLaw H), ∀ i,
      capValue H (reconstructedValues H p i) = p.1 i := by
  have hpair := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) (P.cap H).law
    (fun i => Truncation.tailLaw (P.law i) H)).symm (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
  have hc : ∀ᵐ z ∂Measure.pi (fun i => ((P.cap H).law i).prod (Truncation.tailLaw (P.law i) H)),
      ∀ i, capValue H (Truncation.reconstruct H (z i)) = (z i).1 := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun i => ((P.cap H).law i).prod (Truncation.tailLaw (P.law i) H)) i).quasiMeasurePreserving.ae
      (Truncation.cap_reconstruct_ae (P.law i) H)
  exact hpair.quasiMeasurePreserving.ae hc

variable {Seed : Type*} [MeasurableSpace Seed]

/-- This shuffle groups the capped values with their independent tail seeds, and leaves
clocks grouped with the original policy seed. -/
def reconstructionShuffle (ω : World n (Seed × (Fin n → ℝ))) :
    ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × Seed) :=
  ((ω.1, ω.2.2.2), (ω.2.1, ω.2.2.1))

lemma reconstructionShuffle_measurePreserving (P : Instance n) (H : ℝ≥0) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    MeasurePreserving reconstructionShuffle ((P.cap H).worldLaw (ν.prod (P.tailDrawLaw H)))
      (((P.cap H).valuesLaw.prod (P.tailDrawLaw H)).prod ((clocksLaw n).prod ν)) := by
  have h1 := (MeasurePreserving.id (P.cap H).valuesLaw).prod
    ((MeasurePreserving.id (clocksLaw n)).prod (Measure.measurePreserving_swap (μ := ν) (ν := P.tailDrawLaw H)))
  have h2 := (MeasurePreserving.id (P.cap H).valuesLaw).prod
    ((measurePreserving_prodAssoc (clocksLaw n) (P.tailDrawLaw H) ν).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id (P.cap H).valuesLaw).prod
    ((Measure.measurePreserving_swap (μ := clocksLaw n) (ν := P.tailDrawLaw H)).prod (MeasurePreserving.id ν))
  have h4 := (MeasurePreserving.id (P.cap H).valuesLaw).prod
    (measurePreserving_prodAssoc (P.tailDrawLaw H) (clocksLaw n) ν)
  have h5 := (measurePreserving_prodAssoc (P.cap H).valuesLaw (P.tailDrawLaw H)
    ((clocksLaw n).prod ν)).symm MeasurableEquiv.prodAssoc
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

noncomputable def reconstructedWorld (H : ℝ≥0) (ω : World n (Seed × (Fin n → ℝ))) : World n Seed :=
  (reconstructedValues H (ω.1, ω.2.2.2), (ω.2.1, ω.2.2.1))

lemma reconstructedWorld_measurePreserving (P : Instance n) (H : ℝ≥0) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    MeasurePreserving (reconstructedWorld H) ((P.cap H).worldLaw (ν.prod (P.tailDrawLaw H))) (P.worldLaw ν) :=
  ((P.reconstructedValues_measurePreserving H).prod (MeasurePreserving.id _)).comp
    (P.reconstructionShuffle_measurePreserving H ν)

lemma world_cap_reconstructedValues_ae (P : Instance n) (H : ℝ≥0) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    ∀ᵐ ω : World n (Seed × (Fin n → ℝ)) ∂(P.cap H).worldLaw (ν.prod (P.tailDrawLaw H)), ∀ i,
      capValue H (reconstructedValues H (ω.1, ω.2.2.2) i) = ω.1 i := by
  have hi := (measurePreserving_fst (μ := (P.cap H).valuesLaw.prod (P.tailDrawLaw H))
    (ν := (clocksLaw n).prod ν)).comp (P.reconstructionShuffle_measurePreserving H ν)
  exact hi.quasiMeasurePreserving.ae (P.cap_reconstructedValues_ae H)

noncomputable def capWorld (H : ℝ≥0) (ω : World n Seed) : World n Seed := (capValue H ∘ ω.1, ω.2)

lemma capWorld_measurePreserving (P : Instance n) (H : ℝ≥0) (ν : Measure Seed)
    [IsProbabilityMeasure ν] :
    MeasurePreserving (capWorld H) (P.worldLaw ν) ((P.cap H).worldLaw ν) :=
  (P.capValues_measurePreserving H).prod (MeasurePreserving.id _)

noncomputable def tailFunctional (H : ℝ≥0) (x : Fin n → ℝ) : ℝ := ∑ i, tailValue H (x i)

lemma measurable_tailFunctional (H : ℝ≥0) : Measurable (@tailFunctional n H) := by
  apply Finset.measurable_sum
  intro i _
  exact (measurable_tailValue H).comp (measurable_pi_apply i)

lemma integrable_tailFunctional (P : Instance n) (H : ℝ≥0) (hP : Integrable maximum P.valuesLaw) :
    Integrable (tailFunctional H) P.valuesLaw := by
  apply integrable_finsetSum
  intro i _
  exact (measurePreserving_eval P.law i).integrable_comp_of_integrable
    (integrable_tailValue (P.law i) (P.integrable_maximum_iff.mp hP i) H)

lemma integral_tailFunctional (P : Instance n) (H : ℝ≥0) (hP : Integrable maximum P.valuesLaw) :
    (∫ x, tailFunctional H x ∂P.valuesLaw) = P.tailSum H := by
  change (∫ x : Fin n → ℝ, (∑ i, tailValue H (x i)) ∂P.valuesLaw) =
    ∑ i, ∫ x, tailValue H x ∂P.law i
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    have hp : MeasurePreserving (Function.eval i) P.valuesLaw (P.law i) := measurePreserving_eval P.law i
    have h := integral_map (μ := P.valuesLaw) hp.measurable.aemeasurable
      (measurable_tailValue H).aestronglyMeasurable
    rw [hp.map_eq] at h
    exact h.symm
  · intro i _
    exact (measurePreserving_eval P.law i).integrable_comp_of_integrable
      (integrable_tailValue (P.law i) (P.integrable_maximum_iff.mp hP i) H)

lemma integrable_world_tailFunctional (P : Instance n) (H : ℝ≥0) (hP : Integrable maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    Integrable (fun ω : World n Seed => tailFunctional H ω.1) (P.worldLaw ν) :=
  (measurePreserving_fst (μ := P.valuesLaw) (ν := (clocksLaw n).prod ν)).integrable_comp_of_integrable
    (P.integrable_tailFunctional H hP)

lemma integral_world_tailFunctional (P : Instance n) (H : ℝ≥0) (hP : Integrable maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∫ ω : World n Seed, tailFunctional H ω.1 ∂P.worldLaw ν) = P.tailSum H := by
  have hp : MeasurePreserving (fun ω : World n Seed => ω.1) (P.worldLaw ν) P.valuesLaw := measurePreserving_fst
  have h := integral_map (μ := P.worldLaw ν) hp.measurable.aemeasurable
    (measurable_tailFunctional H).aestronglyMeasurable
  rw [hp.map_eq] at h
  exact h.symm.trans (P.integral_tailFunctional H hP)

end Instance
namespace RandomizedPolicy

variable {n : ℕ}

/-- Full-information reconstruction: the conditional tail laws are known to this policy.
This is not a learner using unknown distributions. -/
noncomputable def reconstructFromCap (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0) :
    RandomizedPolicy n where
  Seed := π.Seed × (Fin n → ℝ)
  seedLaw := π.seedLaw.prod (P.tailDrawLaw H)
  rule := π.rule.pullbackValuesBy Prod.fst
    (fun (r : π.Seed × (Fin n → ℝ)) i y => Truncation.reconstruct H (y, r.2 i))
  measurable_rule := π.rule.pullbackValuesBy_isMeasurable π.measurable_rule Prod.fst measurable_fst
    (fun (r : π.Seed × (Fin n → ℝ)) i y => Truncation.reconstruct H (y, r.2 i)) (fun i =>
      (Truncation.measurable_reconstruct H).comp
        (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst.snd)))

lemma reconstructFromCap_expectedDuration (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0) :
    (π.reconstructFromCap P H).expectedDuration (P.cap H) = π.expectedDuration P := by
  have hp := P.reconstructedWorld_measurePreserving H π.seedLaw
  have heq := integral_map (μ := (P.cap H).worldLaw (π.seedLaw.prod (P.tailDrawLaw H)))
    hp.measurable.aemeasurable π.measurable_realizedDuration.aestronglyMeasurable
  rw [hp.map_eq] at heq
  calc
    (π.reconstructFromCap P H).expectedDuration (P.cap H) =
        ∫ ω, π.realizedDuration (Instance.reconstructedWorld H ω)
          ∂(P.cap H).worldLaw (π.seedLaw.prod (P.tailDrawLaw H)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => π.rule.pullbackValuesBy_stoppingTime Prod.fst
        (fun (r : π.Seed × (Fin n → ℝ)) i y => Truncation.reconstruct H (y, r.2 i)) ω.2.2 Finset.univ ω.1 ω.2.1
    _ = π.expectedDuration P := heq.symm

/-- Reconstructing observations preserves the selected identity and loses at most the
sum of the expected clipped tails. Integrability follows from the finite expected maximum. -/
lemma expectedReward_le_reconstructFromCap (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    π.expectedReward P ≤ (π.reconstructFromCap P H).expectedReward (P.cap H) + P.tailSum H := by
  let ρ := π.reconstructFromCap P H
  let fρ : ProphetSecretary.Model.World n (π.Seed × (Fin n → ℝ)) → ℝ := ρ.realizedReward
  have hp := P.reconstructedWorld_measurePreserving H π.seedLaw
  have hiπ := hp.integrable_comp_of_integrable (π.integrable_realizedReward P hP)
  have hiρ : Integrable fρ ((P.cap H).worldLaw (π.seedLaw.prod (P.tailDrawLaw H))) :=
    ρ.integrable_realizedReward (P.cap H) (P.cap_integrable_maximum H hP)
  have hiT : Integrable (fun ω : ProphetSecretary.Model.World n (π.Seed × (Fin n → ℝ)) =>
      Instance.tailFunctional H (Instance.reconstructedWorld H ω).1)
      ((P.cap H).worldLaw (π.seedLaw.prod (P.tailDrawLaw H))) :=
    hp.integrable_comp_of_integrable (P.integrable_world_tailFunctional H hP π.seedLaw)
  have heπ := integral_map (μ := (P.cap H).worldLaw (π.seedLaw.prod (P.tailDrawLaw H)))
    hp.measurable.aemeasurable π.measurable_realizedReward.aestronglyMeasurable
  rw [hp.map_eq] at heπ
  have heT := integral_map (μ := (P.cap H).worldLaw (π.seedLaw.prod (P.tailDrawLaw H)))
    hp.measurable.aemeasurable ((Instance.measurable_tailFunctional H).comp measurable_fst).aestronglyMeasurable
  rw [hp.map_eq] at heT
  have hTeq : (∫ ω, Instance.tailFunctional H (Instance.reconstructedWorld H ω).1
      ∂(P.cap H).worldLaw (π.seedLaw.prod (P.tailDrawLaw H))) = P.tailSum H := by
    have ht : (∫ ω, Instance.tailFunctional H (Instance.reconstructedWorld H ω).1
        ∂(P.cap H).worldLaw (π.seedLaw.prod (P.tailDrawLaw H))) =
        ∫ ω : ProphetSecretary.Model.World n π.Seed, Instance.tailFunctional H ω.1 ∂P.worldLaw π.seedLaw := by
      simpa only [Function.comp_apply] using heT.symm
    exact ht.trans (P.integral_world_tailFunctional H hP π.seedLaw)
  have hb : ∀ᵐ ω : ProphetSecretary.Model.World n (π.Seed × (Fin n → ℝ))
      ∂(P.cap H).worldLaw (π.seedLaw.prod (P.tailDrawLaw H)),
      π.realizedReward (Instance.reconstructedWorld H ω) ≤
        fρ ω + Instance.tailFunctional H (Instance.reconstructedWorld H ω).1 := by
    filter_upwards [P.world_cap_reconstructedValues_ae H π.seedLaw] with ω hcap
    let X := Instance.reconstructedValues H (ω.1, ω.2.2.2)
    have hgd : ∀ i, X i - ω.1 i ≤ tailValue H (X i) := by
      intro i
      calc
        X i - ω.1 i = X i - capValue H (X i) := by rw [hcap i]
        _ = tailValue H (X i) := sub_capValue_eq_tailValue H (X i)
        _ ≤ tailValue H (X i) := le_rfl
    have hloss := π.rule.pullbackValuesBy_reward_loss_le Prod.fst
      (fun (r : π.Seed × (Fin n → ℝ)) i y => Truncation.reconstruct H (y, r.2 i)) ω.2.2 Finset.univ ω.1 ω.2.1
      (fun i => tailValue H (X i)) (fun i => tailValue_nonnegative H (X i)) hgd
    change π.realizedReward (Instance.reconstructedWorld H ω) - fρ ω ≤
      Instance.tailFunctional H (Instance.reconstructedWorld H ω).1 at hloss
    linarith
  have h := integral_mono_ae hiπ (hiρ.add hiT) hb
  change (∫ ω, π.realizedReward (Instance.reconstructedWorld H ω)
      ∂(P.cap H).worldLaw (π.seedLaw.prod (P.tailDrawLaw H))) ≤
    ∫ ω, fρ ω + Instance.tailFunctional H (Instance.reconstructedWorld H ω).1
      ∂(P.cap H).worldLaw (π.seedLaw.prod (P.tailDrawLaw H)) at h
  rw [integral_add hiρ hiT, hTeq, ← heπ] at h
  change π.expectedReward P ≤ (∫ ω, fρ ω ∂(P.cap H).worldLaw (π.seedLaw.prod (P.tailDrawLaw H))) + P.tailSum H
  exact h

lemma scalarObjective_le_reconstructFromCap (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) :
    π.scalarObjective P w c ≤ (π.reconstructFromCap P H).scalarObjective (P.cap H) w c + w * P.tailSum H := by
  rw [π.scalarObjective_eq P hP,
    (π.reconstructFromCap P H).scalarObjective_eq (P.cap H) (P.cap_integrable_maximum H hP),
    reconstructFromCap_expectedDuration]
  have h := mul_le_mul_of_nonneg_left (π.expectedReward_le_reconstructFromCap P H hP) hw
  linarith

lemma expectedDuration_cap (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0) :
    π.expectedDuration (P.cap H) = (π.pullbackValues (capValue H) (measurable_capValue H)).expectedDuration P := by
  have hp := P.capWorld_measurePreserving H π.seedLaw
  have heq := integral_map (μ := P.worldLaw π.seedLaw) hp.measurable.aemeasurable
    π.measurable_realizedDuration.aestronglyMeasurable
  rw [hp.map_eq] at heq
  calc
    π.expectedDuration (P.cap H) = ∫ ω, π.realizedDuration (Instance.capWorld H ω) ∂P.worldLaw π.seedLaw := heq
    _ = (π.pullbackValues (capValue H) (measurable_capValue H)).expectedDuration P := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω =>
        (π.rule.pullbackValues_stoppingTime (capValue H) ω.2.2 Finset.univ ω.1 ω.2.1).symm

lemma expectedReward_cap_le_pullback (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    π.expectedReward (P.cap H) ≤ (π.pullbackValues (capValue H) (measurable_capValue H)).expectedReward P := by
  have hp := P.capWorld_measurePreserving H π.seedLaw
  have heq := integral_map (μ := P.worldLaw π.seedLaw) hp.measurable.aemeasurable
    π.measurable_realizedReward.aestronglyMeasurable
  rw [hp.map_eq] at heq
  calc
    π.expectedReward (P.cap H) = ∫ ω, π.realizedReward (Instance.capWorld H ω) ∂P.worldLaw π.seedLaw := heq
    _ ≤ (π.pullbackValues (capValue H) (measurable_capValue H)).expectedReward P := by
      exact integral_mono
        (hp.integrable_comp_of_integrable (π.integrable_realizedReward (P.cap H) (P.cap_integrable_maximum H hP)))
        ((π.pullbackValues (capValue H) (measurable_capValue H)).integrable_realizedReward P hP)
        (fun ω => π.rule.reward_cap_le_pullback H ω.2.2 Finset.univ ω.1 ω.2.1)

lemma scalarObjective_cap_le_pullback (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) :
    π.scalarObjective (P.cap H) w c ≤
      (π.pullbackValues (capValue H) (measurable_capValue H)).scalarObjective P w c := by
  rw [π.scalarObjective_eq (P.cap H) (P.cap_integrable_maximum H hP),
    (π.pullbackValues (capValue H) (measurable_capValue H)).scalarObjective_eq P hP,
    expectedDuration_cap]
  exact add_le_add (mul_le_mul_of_nonneg_left (π.expectedReward_cap_le_pullback P H hP) hw) le_rfl

end RandomizedPolicy

lemma optimalScalarValue_le_cap_add_tail {n : ℕ} (P : Instance n) (H : ℝ≥0)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue P w c ≤ optimalScalarValue (P.cap H) w c + w * P.tailSum H := by
  apply csSup_le (scalarValues_nonempty P w c)
  rintro v ⟨π, rfl⟩
  exact (π.scalarObjective_le_reconstructFromCap P H hP hw).trans
    (add_le_add (scalarObjective_le_optimal _ (P.cap H) (P.cap_integrable_maximum H hP) hw hc) le_rfl)

lemma optimalScalarValue_cap_le {n : ℕ} (P : Instance n) (H : ℝ≥0)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue (P.cap H) w c ≤ optimalScalarValue P w c := by
  apply csSup_le (scalarValues_nonempty (P.cap H) w c)
  rintro v ⟨π, rfl⟩
  exact (π.scalarObjective_cap_le_pullback P H hP hw).trans
    (scalarObjective_le_optimal _ P hP hw hc)

/-- Fixed-finite-instance scalar values converge through explicit policy transports. -/
lemma optimalScalarValue_cap_tendsto {n : ℕ} (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Tendsto (fun H : ℝ≥0 => optimalScalarValue (P.cap H) w c) atTop (𝓝 (optimalScalarValue P w c)) := by
  have hl : Tendsto (fun H : ℝ≥0 => optimalScalarValue P w c - w * P.tailSum H)
      atTop (𝓝 (optimalScalarValue P w c)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul (P.tailSum_tendsto_zero hP))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
  · intro H
    have h := optimalScalarValue_le_cap_add_tail P H hP hw hc
    linarith
  · intro H
    exact optimalScalarValue_cap_le P H hP hw hc

end ProphetSecretary.Model
