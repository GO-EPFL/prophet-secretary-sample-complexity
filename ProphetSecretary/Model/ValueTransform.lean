import ProphetSecretary.Model.Truncation

/-!
# Coordinate-wise transformations of offer values

The product law and its independent clocks/seed are pushed forward explicitly.
The causal policy pullback reuses the existing history map, retaining identities
and observations of zero values. Since at most one occurrence is selected, a
uniform value displacement costs at most that displacement, independent of n.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.mapValues (P : Instance n) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x) : Instance n where
  law i := (P.law i).map (f i)
  probability i := Measure.isProbabilityMeasure_map (hf i).aemeasurable
  nonnegative i := (ae_map_iff (hf i).aemeasurable measurableSet_Ici).mpr (hnn i)

lemma Instance.mapValues_measurePreserving (P : Instance n) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x) :
    MeasurePreserving (fun x : Fin n → ℝ => fun i => f i (x i)) P.valuesLaw
      (P.mapValues f hf hnn).valuesLaw :=
  ⟨measurable_pi_lambda _ (fun i => (hf i).comp (measurable_pi_apply i)),
    Measure.pi_map_pi (fun i => (hf i).aemeasurable)⟩

def transformWorld {Seed : Type*} (f : Fin n → ℝ → ℝ) (ω : World n Seed) : World n Seed :=
  (fun i => f i (ω.1 i), ω.2)

lemma Instance.transformWorld_measurePreserving {Seed : Type*} [MeasurableSpace Seed]
    (P : Instance n) (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (transformWorld f) (P.worldLaw ν) ((P.mapValues f hf hnn).worldLaw ν) :=
  (P.mapValues_measurePreserving f hf hnn).prod (MeasurePreserving.id _)

lemma Instance.mapValues_integrable_maximum (P : Instance n) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    (hInt : ∀ i, Integrable (f i) (P.law i)) :
    Integrable Instance.maximum (P.mapValues f hf hnn).valuesLaw := by
  apply (P.mapValues f hf hnn).integrable_maximum_iff.mpr
  intro i
  exact (integrable_map_measure aestronglyMeasurable_id (hf i).aemeasurable).mpr (hInt i)

lemma Instance.integrable_valueTransform_of_bounded_displacement (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) {h : ℝ}
    (hdispl : ∀ i, ∀ᵐ x ∂P.law i, |f i x - x| ≤ h) :
    ∀ i, Integrable (f i) (P.law i) := by
  intro i
  have hdom := ((P.integrable_maximum_iff.mp hP i).abs).add (integrable_const h)
  apply hdom.mono' (hf i).aestronglyMeasurable
  filter_upwards [hdispl i] with x hx
  rw [Real.norm_eq_abs]
  calc
    |f i x| = |(f i x - x) + x| := by congr 1; ring
    _ ≤ |f i x - x| + |x| := abs_add_le _ _
    _ ≤ h + |x| := add_le_add hx le_rfl
    _ = _ := add_comm _ _

lemma Policy.pullbackValuesBy_reward_abs_difference_le {Seed NewSeed : Type*}
    (π : Policy Seed n) (s : NewSeed → Seed) (g : NewSeed → Fin n → ℝ → ℝ)
    (r : NewSeed) (D : Finset (Fin n)) (x u : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hdispl : ∀ i, |g r i (x i) - x i| ≤ h) :
    |π.reward (s r) D (fun i => g r i (x i)) u - (π.pullbackValuesBy s g).reward r D x u| ≤ h := by
  by_cases hsel : ∃ i, π.ActualSelects (s r) D (fun i => g r i (x i)) u i
  · obtain ⟨i, hi⟩ := hsel
    have hpi := (π.pullbackValuesBy_actualSelects_iff s g r D x u i).mpr hi
    rw [π.reward_eq_of_actualSelects (s r) D _ u hi,
      (π.pullbackValuesBy s g).reward_eq_of_actualSelects r D x u hpi]
    exact hdispl i
  · have hπ : ∀ i, ¬π.ActualSelects (s r) D (fun i => g r i (x i)) u i :=
      fun i hi => hsel ⟨i, hi⟩
    have hpi : ∀ i, ¬(π.pullbackValuesBy s g).ActualSelects r D x u i :=
      fun i hi => hπ i ((π.pullbackValuesBy_actualSelects_iff s g r D x u i).mp hi)
    rw [π.reward_eq_zero_of_no_actualSelection _ _ _ _ hπ,
      (π.pullbackValuesBy s g).reward_eq_zero_of_no_actualSelection _ _ _ _ hpi, sub_self, abs_zero]
    exact hh

noncomputable def RandomizedPolicy.pullbackValuesIndexed (π : RandomizedPolicy n)
    (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i)) : RandomizedPolicy n where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := π.rule.pullbackValuesBy id (fun _ => f)
  measurable_rule := π.rule.pullbackValuesBy_isMeasurable π.measurable_rule id measurable_id
    (fun _ => f) (fun i => (hf i).comp measurable_snd)

lemma RandomizedPolicy.expectedDuration_mapValues (π : RandomizedPolicy n) (P : Instance n)
    (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x) :
    π.expectedDuration (P.mapValues f hf hnn) = (π.pullbackValuesIndexed f hf).expectedDuration P := by
  have hmap := P.transformWorld_measurePreserving f hf hnn π.seedLaw
  have heq := integral_map (μ := P.worldLaw π.seedLaw) hmap.measurable.aemeasurable
    π.measurable_realizedDuration.aestronglyMeasurable
  rw [hmap.map_eq] at heq
  calc
    _ = ∫ ω : ProphetSecretary.Model.World n π.Seed, π.rule.stoppingTime ω.2.2 Finset.univ
        (fun i => f i (ω.1 i)) ω.2.1 ∂P.worldLaw π.seedLaw := heq
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω =>
        (π.rule.pullbackValuesBy_stoppingTime id (fun _ => f) ω.2.2 Finset.univ ω.1 ω.2.1).symm

lemma Instance.mapValues_integrable_of_bounded_displacement (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x)
    {h : ℝ} (hdispl : ∀ i, ∀ᵐ x ∂P.law i, |f i x - x| ≤ h) :
    Integrable Instance.maximum (P.mapValues f hf hnn).valuesLaw :=
  P.mapValues_integrable_maximum f hf hnn
    (P.integrable_valueTransform_of_bounded_displacement hP f hf hdispl)

/-- The reward displacement has no factor depending on instance size. Both
expectations use the actual transformed/base product laws and the same seed law. -/
theorem RandomizedPolicy.expectedReward_mapValues_abs_difference_le (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x) {h : ℝ} (hh : 0 ≤ h)
    (hdispl : ∀ i, ∀ᵐ x ∂P.law i, |f i x - x| ≤ h) :
    |π.expectedReward (P.mapValues f hf hnn) - (π.pullbackValuesIndexed f hf).expectedReward P| ≤ h := by
  let Q := P.mapValues f hf hnn
  let πP := π.pullbackValuesIndexed f hf
  let F : ProphetSecretary.Model.World n π.Seed → ℝ := fun ω =>
    π.rule.reward ω.2.2 Finset.univ (fun i => f i (ω.1 i)) ω.2.1
  let G : ProphetSecretary.Model.World n π.Seed → ℝ := fun ω =>
    (π.rule.pullbackValuesBy id (fun _ => f)).reward ω.2.2 Finset.univ ω.1 ω.2.1
  have hQ := P.mapValues_integrable_of_bounded_displacement hP f hf hnn hdispl
  have hmap := P.transformWorld_measurePreserving f hf hnn π.seedLaw
  have hF : Integrable F (P.worldLaw π.seedLaw) :=
    hmap.integrable_comp_of_integrable (π.integrable_realizedReward Q hQ)
  have hG : Integrable G (P.worldLaw π.seedLaw) := πP.integrable_realizedReward P hP
  have heqF : (∫ ω, F ω ∂P.worldLaw π.seedLaw) = π.expectedReward Q := by
    have heq := integral_map (μ := P.worldLaw π.seedLaw) hmap.measurable.aemeasurable
      π.measurable_realizedReward.aestronglyMeasurable
    rw [hmap.map_eq] at heq
    exact heq.symm
  have heqG : (∫ ω, G ω ∂P.worldLaw π.seedLaw) = πP.expectedReward P := rfl
  have hvals : ∀ᵐ x ∂P.valuesLaw, ∀ i, |f i (x i) - x i| ≤ h := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hdispl i)
  have hp : MeasurePreserving (fun ω : ProphetSecretary.Model.World n π.Seed => ω.1)
      (P.worldLaw π.seedLaw) P.valuesLaw := measurePreserving_fst
  have hbound : ∀ᵐ ω ∂P.worldLaw π.seedLaw, ‖F ω - G ω‖ ≤ h := by
    filter_upwards [hp.quasiMeasurePreserving.ae hvals] with ω hω
    rw [Real.norm_eq_abs]
    exact π.rule.pullbackValuesBy_reward_abs_difference_le id (fun _ => f) ω.2.2
      Finset.univ ω.1 ω.2.1 hh hω
  have hn := norm_integral_le_of_norm_le_const hbound
  rw [integral_sub hF hG, heqF, heqG] at hn
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hn

/-- Pulling a policy back along the observed value transformation preserves its
duration and changes its scalar objective by at most w times the displacement. -/
theorem RandomizedPolicy.scalarObjective_mapValues_le (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x) {h w : ℝ} (hh : 0 ≤ h) (hw : 0 ≤ w) (c : ℝ)
    (hdispl : ∀ i, ∀ᵐ x ∂P.law i, |f i x - x| ≤ h) :
    π.scalarObjective (P.mapValues f hf hnn) w c ≤
      (π.pullbackValuesIndexed f hf).scalarObjective P w c + w * h := by
  have hQ := P.mapValues_integrable_of_bounded_displacement hP f hf hnn hdispl
  have habs := π.expectedReward_mapValues_abs_difference_le P hP f hf hnn hh hdispl
  have hR := (le_abs_self _).trans habs
  have hRw := mul_le_mul_of_nonneg_left hR hw
  rw [π.scalarObjective_eq _ hQ, (π.pullbackValuesIndexed f hf).scalarObjective_eq P hP,
    π.expectedDuration_mapValues P f hf hnn]
  nlinarith only [hRw]

end ProphetSecretary.Model
