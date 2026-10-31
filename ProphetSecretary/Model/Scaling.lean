import ProphetSecretary.Model.ScalarObjectiveBounds
import Mathlib.Algebra.Order.GroupWithZero.Finset

/-!
# Value transformations and scaling

A value pullback applies a measurable map to the current value and to every observed
history value, retaining identities, timestamps, and the occurrence of zero observations.
Positive scaling transports arbitrary randomized history-dependent policies in both
directions, rather than restricting the policy class to thresholds or finite supports.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

noncomputable def mapObservationValues (g : ℝ → ℝ) : Option (ℝ × ℝ) → Option (ℝ × ℝ)
  | none => none
  | some p => some (p.1, g p.2)

noncomputable def mapHistoryValues {n : ℕ} (g : ℝ → ℝ) (h : History n) : History n :=
  fun i => mapObservationValues g (h i)

noncomputable def Policy.pullbackValues {Seed : Type*} {n : ℕ}
    (π : Policy Seed n) (g : ℝ → ℝ) : Policy Seed n where
  decide r t i v h := π.decide r t i (g v) (mapHistoryValues g h)

variable {Seed : Type*} {n : ℕ}

theorem mapHistoryValues_history (g : ℝ → ℝ) (D : Finset (Fin n))
    (x u : Fin n → ℝ) (t : ℝ) :
    mapHistoryValues g (history D x u t) = history D (g ∘ x) u t := by
  funext i
  by_cases hi : i ∈ D ∧ u i < t
  · simp [mapHistoryValues, mapObservationValues, history, hi]
  · simp [mapHistoryValues, mapObservationValues, history, hi]

theorem Policy.pullbackValues_action (π : Policy Seed n) (g : ℝ → ℝ) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) :
    (π.pullbackValues g).action r D x u i = π.action r D (g ∘ x) u i := by
  simp only [Policy.action, Policy.pullbackValues, mapHistoryValues_history, Function.comp_apply]

theorem Policy.pullbackValues_accepted (π : Policy Seed n) (g : ℝ → ℝ) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    (π.pullbackValues g).accepted r D x u = π.accepted r D (g ∘ x) u := by
  ext i
  simp only [Policy.mem_accepted, Policy.pullbackValues_action]

theorem Policy.pullbackValues_stoppingTime (π : Policy Seed n) (g : ℝ → ℝ) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    (π.pullbackValues g).stoppingTime r D x u = π.stoppingTime r D (g ∘ x) u := by
  unfold Policy.stoppingTime Policy.stopTimes
  simp only [Policy.pullbackValues_accepted]

theorem Policy.pullbackValues_selects_iff (π : Policy Seed n) (g : ℝ → ℝ) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) :
    (π.pullbackValues g).Selects r D x u i ↔ π.Selects r D (g ∘ x) u i := by
  simp only [Policy.Selects, Policy.pullbackValues_accepted, Policy.pullbackValues_stoppingTime]

theorem Policy.pullbackValues_actualSelects_iff (π : Policy Seed n) (g : ℝ → ℝ) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) :
    (π.pullbackValues g).ActualSelects r D x u i ↔ π.ActualSelects r D (g ∘ x) u i := by
  simp only [Policy.ActualSelects, Policy.pullbackValues_selects_iff]

/-- Mapping selected values by a scalar maps the realized reward by that scalar.
The no-selection convention is preserved because scalar multiplication fixes zero. -/
theorem Policy.reward_scale_pullback (π : Policy Seed n) (a : ℝ) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    π.reward r D (fun i => a * x i) u = a * (π.pullbackValues (a * ·)).reward r D x u := by
  unfold Policy.reward
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := π.pullbackValues_actualSelects_iff (a * ·) r D x u i
  by_cases hi : (π.pullbackValues (a * ·)).ActualSelects r D x u i
  · have hgi := he.mp hi
    simp only [Function.comp_def] at hgi
    simp only [if_pos hi, if_pos hgi]
  · have hgi : ¬π.ActualSelects r D ((a * ·) ∘ x) u i := fun h => hi (he.mpr h)
    simp only [Function.comp_def] at hgi
    simp only [if_neg hi, if_neg hgi, mul_zero]

theorem mapHistoryValues_comp (g h : ℝ → ℝ) (H : History n) :
    mapHistoryValues g (mapHistoryValues h H) = mapHistoryValues (g ∘ h) H := by
  funext i
  simp only [mapHistoryValues]
  cases H i <;> rfl

theorem mapHistoryValues_id (H : History n) : mapHistoryValues id H = H := by
  funext i
  simp only [mapHistoryValues]
  cases H i <;> rfl

theorem Policy.pullbackValues_comp (π : Policy Seed n) (g h : ℝ → ℝ) :
    (π.pullbackValues g).pullbackValues h = π.pullbackValues (g ∘ h) := by
  cases π
  unfold Policy.pullbackValues
  congr 1
  funext r t i v H
  simp only [mapHistoryValues_comp, Function.comp_apply]

theorem Policy.pullbackValues_id (π : Policy Seed n) : π.pullbackValues id = π := by
  cases π
  unfold Policy.pullbackValues
  congr 1
  funext r t i v H
  simp only [mapHistoryValues_id, id_eq]

private def observationEncode : Option (ℝ × ℝ) → Unit ⊕ (ℝ × ℝ)
  | none => Sum.inl ()
  | some p => Sum.inr p

private theorem measurable_observationEncode : Measurable observationEncode :=
  Measurable.of_comap_le le_rfl

theorem measurable_mapObservationValues {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (mapObservationValues g) := by
  rw [measurable_comap_iff]
  have h : Measurable (fun o => Sum.elim
      (fun _ : Unit => (Sum.inl () : Unit ⊕ (ℝ × ℝ)))
      (fun p : ℝ × ℝ => Sum.inr (p.1, g p.2)) (observationEncode o)) :=
    (measurable_const.sumElim (measurable_inr.comp
      (measurable_fst.prodMk (hg.comp measurable_snd)))).comp measurable_observationEncode
  convert h using 1
  funext o
  cases o <;> rfl

theorem measurable_mapHistoryValues {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (@mapHistoryValues n g) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_mapObservationValues hg).comp (measurable_pi_apply i)

variable [MeasurableSpace Seed]

theorem Policy.pullbackValues_isMeasurable (π : Policy Seed n) (hπ : π.IsMeasurable)
    {g : ℝ → ℝ} (hg : Measurable g) : (π.pullbackValues g).IsMeasurable := by
  exact hπ.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
    (measurable_snd.snd.fst.prodMk ((hg.comp measurable_snd.snd.snd.fst).prodMk
      ((measurable_mapHistoryValues hg).comp measurable_snd.snd.snd.snd)))))

theorem measurable_valueScale (a : ℝ) : Measurable (fun x : ℝ => a * x) :=
  measurable_const.mul measurable_id

namespace Instance

/-- Multiply each offer by a nonnegative scalar, preserving the independent product law. -/
noncomputable def scale (P : Instance n) (a : ℝ) (ha : 0 ≤ a) : Instance n where
  law i := (P.law i).map (a * ·)
  probability i := Measure.isProbabilityMeasure_map (measurable_valueScale a).aemeasurable
  nonnegative i := by
    apply (ae_map_iff (measurable_valueScale a).aemeasurable measurableSet_Ici).mpr
    exact (P.nonnegative i).mono fun x hx => mul_nonneg ha hx

/-- The realized maximum includes zero for the empty instance, so this identity also
holds at scale zero and when some coordinates are negative outside the offer support. -/
theorem maximum_scale (a : ℝ) (ha : 0 ≤ a) (x : Fin n → ℝ) :
    maximum (fun i => a * x i) = a * maximum x := by
  unfold maximum
  have h := (Finset.mul₀_sup' ha (fun j : Option (Fin n) => j.elim 0 x)
    Finset.univ ⟨none, Finset.mem_univ _⟩).symm
  convert h using 1
  congr 1
  funext j
  cases j <;> simp

/-- The complete transformed offer vector has exactly the scaled product law. -/
theorem scaleValues_measurePreserving (P : Instance n) (a : ℝ) (ha : 0 ≤ a) :
    MeasurePreserving (fun x : Fin n → ℝ => fun i => a * x i) P.valuesLaw (P.scale a ha).valuesLaw := by
  refine ⟨?_, ?_⟩
  · apply measurable_pi_lambda
    intro i
    exact measurable_const.mul (measurable_pi_apply i)
  · exact Measure.pi_map_pi (fun _ => (measurable_valueScale a).aemeasurable)

noncomputable def scaleWorld (a : ℝ) (ω : World n Seed) : World n Seed :=
  (fun i => a * ω.1 i, ω.2)

theorem scaleWorld_measurePreserving (P : Instance n) (a : ℝ) (ha : 0 ≤ a)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (scaleWorld a) (P.worldLaw ν) ((P.scale a ha).worldLaw ν) :=
  (P.scaleValues_measurePreserving a ha).prod (MeasurePreserving.id _)

theorem scale_integrable_maximum (P : Instance n) (a : ℝ) (ha : 0 ≤ a)
    (hP : Integrable maximum P.valuesLaw) : Integrable maximum (P.scale a ha).valuesLaw := by
  apply ((P.scaleValues_measurePreserving a ha).integrable_comp measurable_maximum.aestronglyMeasurable).mp
  simpa only [Function.comp_def, maximum_scale a ha] using hP.const_mul a

theorem scale_expectedMaximum (P : Instance n) (a : ℝ) (ha : 0 ≤ a) :
    (P.scale a ha).expectedMaximum = a * P.expectedMaximum := by
  have h := integral_map (μ := P.valuesLaw) (P.scaleValues_measurePreserving a ha).measurable.aemeasurable
    measurable_maximum.aestronglyMeasurable
  rw [(P.scaleValues_measurePreserving a ha).map_eq] at h
  calc
    (P.scale a ha).expectedMaximum = ∫ x, maximum (fun i => a * x i) ∂P.valuesLaw := h
    _ = a * P.expectedMaximum := by simp only [maximum_scale a ha, integral_const_mul, expectedMaximum]

theorem ext_law {P Q : Instance n} (h : P.law = Q.law) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- The inverse scale is proved at the marginal law level, not merely at the value level. -/
theorem scale_inv (P : Instance n) (a : ℝ) (ha : 0 < a) :
    (P.scale a ha.le).scale a⁻¹ (inv_nonneg.mpr ha.le) = P := by
  apply ext_law
  funext i
  change ((P.law i).map (a * ·)).map (a⁻¹ * ·) = P.law i
  rw [Measure.map_map (measurable_valueScale a⁻¹) (measurable_valueScale a)]
  have he : (fun x : ℝ => a⁻¹ * (a * x)) = id := by
    funext x
    simp [ha.ne']
  rw [show ((a⁻¹ * ·) ∘ (a * ·)) = id from he, Measure.map_id]

theorem scale_inv_left (P : Instance n) (a : ℝ) (ha : 0 < a) :
    (P.scale a⁻¹ (inv_nonneg.mpr ha.le)).scale a ha.le = P := by
  simpa only [inv_inv] using P.scale_inv a⁻¹ (inv_pos.mpr ha)

theorem hasPositiveFiniteMaximum_scale (P : Instance n) (a : ℝ) (ha : 0 < a)
    (hP : P.HasPositiveFiniteMaximum) : (P.scale a ha.le).HasPositiveFiniteMaximum := by
  refine ⟨P.scale_integrable_maximum a ha.le hP.1, ?_⟩
  rw [P.scale_expectedMaximum a ha.le]
  exact mul_pos ha hP.2

end Instance

omit [MeasurableSpace Seed] in
theorem Policy.pullbackValues_inverse_scale (π : Policy Seed n) (a : ℝ) (ha : a ≠ 0) :
    (π.pullbackValues (a⁻¹ * ·)).pullbackValues (a * ·) = π := by
  rw [Policy.pullbackValues_comp]
  have he : ((a⁻¹ * ·) ∘ (a * ·)) = (id : ℝ → ℝ) := by
    funext x
    simp [ha]
  rw [he, Policy.pullbackValues_id]

omit [MeasurableSpace Seed] in
theorem Policy.pullbackValues_scale_inverse (π : Policy Seed n) (a : ℝ) (ha : a ≠ 0) :
    (π.pullbackValues (a * ·)).pullbackValues (a⁻¹ * ·) = π := by
  simpa only [inv_inv] using π.pullbackValues_inverse_scale a⁻¹ (inv_ne_zero ha)

namespace RandomizedPolicy

/-- The transformed policy retains its original auxiliary probability space. -/
noncomputable def pullbackValues (π : RandomizedPolicy n) (g : ℝ → ℝ) (hg : Measurable g) :
    RandomizedPolicy n where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := π.rule.pullbackValues g
  measurable_rule := π.rule.pullbackValues_isMeasurable π.measurable_rule hg

theorem pullbackValues_inverse_scale (π : RandomizedPolicy n) (a : ℝ) (ha : a ≠ 0) :
    (π.pullbackValues (a⁻¹ * ·) (measurable_valueScale a⁻¹)).pullbackValues
      (a * ·) (measurable_valueScale a) = π := by
  cases π
  simp only [pullbackValues, Policy.pullbackValues_inverse_scale _ a ha]

theorem expectedReward_scale (π : RandomizedPolicy n) (P : Instance n) (a : ℝ) (ha : 0 ≤ a) :
    π.expectedReward (P.scale a ha) =
      a * (π.pullbackValues (a * ·) (measurable_valueScale a)).expectedReward P := by
  have hp := P.scaleWorld_measurePreserving a ha π.seedLaw
  have heq := integral_map (μ := P.worldLaw π.seedLaw) hp.measurable.aemeasurable
    π.measurable_realizedReward.aestronglyMeasurable
  rw [hp.map_eq] at heq
  calc
    π.expectedReward (P.scale a ha) =
        ∫ ω : π.World, π.realizedReward (Instance.scaleWorld a ω) ∂P.worldLaw π.seedLaw := heq
    _ = ∫ ω : π.World, a * (π.pullbackValues (a * ·) (measurable_valueScale a)).realizedReward ω
        ∂P.worldLaw π.seedLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => π.rule.reward_scale_pullback a ω.2.2 Finset.univ ω.1 ω.2.1
    _ = a * (π.pullbackValues (a * ·) (measurable_valueScale a)).expectedReward P := by
      rw [integral_const_mul]
      rfl

theorem expectedDuration_scale (π : RandomizedPolicy n) (P : Instance n) (a : ℝ) (ha : 0 ≤ a) :
    π.expectedDuration (P.scale a ha) =
      (π.pullbackValues (a * ·) (measurable_valueScale a)).expectedDuration P := by
  have hp := P.scaleWorld_measurePreserving a ha π.seedLaw
  have heq := integral_map (μ := P.worldLaw π.seedLaw) hp.measurable.aemeasurable
    π.measurable_realizedDuration.aestronglyMeasurable
  rw [hp.map_eq] at heq
  calc
    π.expectedDuration (P.scale a ha) =
        ∫ ω : π.World, π.realizedDuration (Instance.scaleWorld a ω) ∂P.worldLaw π.seedLaw := heq
    _ = (π.pullbackValues (a * ·) (measurable_valueScale a)).expectedDuration P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        (π.rule.pullbackValues_stoppingTime (a * ·) ω.2.2 Finset.univ ω.1 ω.2.1).symm

/-- Transport of a fixed policy's scalar payoff. This does not differentiate or
reoptimize the policy. -/
theorem scalarObjective_scale (π : RandomizedPolicy n) (P : Instance n) (a : ℝ) (ha : 0 ≤ a)
    (hP : Integrable Instance.maximum P.valuesLaw) (w c : ℝ) :
    π.scalarObjective (P.scale a ha) w c =
      (π.pullbackValues (a * ·) (measurable_valueScale a)).scalarObjective P (a * w) c := by
  rw [π.scalarObjective_eq (P.scale a ha) (P.scale_integrable_maximum a ha hP),
    (π.pullbackValues (a * ·) (measurable_valueScale a)).scalarObjective_eq P hP,
    expectedReward_scale, expectedDuration_scale]
  ring

end RandomizedPolicy

/-- Scaling offers transports the full admissible policy class bijectively. In particular
the optimal value identity is independent of canonical-policy existence. -/
theorem optimalScalarValue_scale (P : Instance n) (a : ℝ) (ha : 0 < a)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue (P.scale a ha.le) w c = optimalScalarValue P (a * w) c := by
  apply le_antisymm
  · apply csSup_le (scalarValues_nonempty (P.scale a ha.le) w c)
    rintro v ⟨π, rfl⟩
    rw [π.scalarObjective_scale P a ha.le hP]
    exact scalarObjective_le_optimal _ P hP (mul_nonneg ha.le hw) hc
  · apply csSup_le (scalarValues_nonempty P (a * w) c)
    rintro v ⟨π, rfl⟩
    let π' := π.pullbackValues (a⁻¹ * ·) (measurable_valueScale a⁻¹)
    have he := π'.scalarObjective_scale P a ha.le hP w c
    rw [show π'.pullbackValues (a * ·) (measurable_valueScale a) = π from
      π.pullbackValues_inverse_scale a ha.ne'] at he
    rw [← he]
    exact scalarObjective_le_optimal π' (P.scale a ha.le) (P.scale_integrable_maximum a ha.le hP) hw hc

end ProphetSecretary.Model
