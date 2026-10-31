import ProphetSecretary.Reach.TailLifting

/-!
# Downward rounding after capping

A fixed measurable display map `g` rounds values in `[0,H]` downward, keeps the cap,
and loses at most `δ` at each displayed value. The maximum therefore loses at most
`δ`, independently of the number of offers. An outer-pilot-selected map can be treated
by conditioning on that pilot; it is not treated as a fixed map after inner training.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

lemma Policy.reward_display_le_pullback (π : Policy Seed n) (g : ℝ → ℝ) (r : Seed)
    (x u : Fin n → ℝ) (hdown : ∀ i, g (x i) ≤ x i) :
    π.reward r Finset.univ (g ∘ x) u ≤ (π.pullbackValues g).reward r Finset.univ x u := by
  unfold Policy.reward
  apply Finset.sum_le_sum
  intro i _
  have he := π.pullbackValues_actualSelects_iff g r Finset.univ x u i
  by_cases hi : π.ActualSelects r Finset.univ (g ∘ x) u i
  · have hl := he.mpr hi
    simp only [if_pos hi, if_pos hl, Function.comp_apply]
    exact hdown i
  · have hl : ¬(π.pullbackValues g).ActualSelects r Finset.univ x u i := fun h => hi (he.mp h)
    simp only [if_neg hi, if_neg hl, le_refl]

lemma downward_display_preserves_zero (H : ℝ≥0) (g : ℝ → ℝ)
    (hgnonneg : ∀ x ∈ Icc (0 : ℝ) H, 0 ≤ g x)
    (hgdown : ∀ x ∈ Icc (0 : ℝ) H, g x ≤ x) : g 0 = 0 :=
  le_antisymm (hgdown 0 ⟨le_rfl, H.property⟩) (hgnonneg 0 ⟨le_rfl, H.property⟩)

namespace Instance

/-- Independent rounded displays of a capped instance. The map is fixed at this stage. -/
noncomputable def roundedCap (P : Instance n) (H : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g)
    (hgnonneg : ∀ x ∈ Icc (0 : ℝ) H, 0 ≤ g x) : Instance n where
  law i := ((P.cap H).law i).map g
  probability i := Measure.isProbabilityMeasure_map hg.aemeasurable
  nonnegative i := by
    apply (ae_map_iff hg.aemeasurable measurableSet_Ici).mpr
    filter_upwards [(P.cap H).nonnegative i, P.cap_bounded H i] with x hx0 hxH
    exact hgnonneg x ⟨hx0, hxH⟩

lemma roundedValues_measurePreserving (P : Instance n) (H : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g)
    (hgnonneg : ∀ x ∈ Icc (0 : ℝ) H, 0 ≤ g x) :
    MeasurePreserving (fun x : Fin n → ℝ => g ∘ x) (P.cap H).valuesLaw
      (P.roundedCap H g hg hgnonneg).valuesLaw := by
  refine ⟨by fun_prop, ?_⟩
  exact Measure.pi_map_pi (fun _ => hg.aemeasurable)

lemma roundedCap_bounded (P : Instance n) (H : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g)
    (hgnonneg : ∀ x ∈ Icc (0 : ℝ) H, 0 ≤ g x)
    (hgdown : ∀ x ∈ Icc (0 : ℝ) H, g x ≤ x) (i : Fin n) :
    ∀ᵐ x ∂(P.roundedCap H g hg hgnonneg).law i, x ≤ (H : ℝ) := by
  apply (ae_map_iff hg.aemeasurable measurableSet_Iic).mpr
  filter_upwards [(P.cap H).nonnegative i, P.cap_bounded H i] with x hx0 hxH
  exact (hgdown x ⟨hx0, hxH⟩).trans hxH

lemma roundedCap_integrable_maximum (P : Instance n) (H : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g)
    (hgnonneg : ∀ x ∈ Icc (0 : ℝ) H, 0 ≤ g x)
    (hgdown : ∀ x ∈ Icc (0 : ℝ) H, g x ≤ x) :
    Integrable maximum (P.roundedCap H g hg hgnonneg).valuesLaw :=
  (P.roundedCap H g hg hgnonneg).integrable_maximum_of_bounded
    (P.roundedCap_bounded H g hg hgnonneg hgdown)

variable [MeasurableSpace Seed]

noncomputable def roundedWorld (g : ℝ → ℝ) (ω : World n Seed) : World n Seed := (g ∘ ω.1, ω.2)

lemma roundedWorld_measurePreserving (P : Instance n) (H : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g)
    (hgnonneg : ∀ x ∈ Icc (0 : ℝ) H, 0 ≤ g x) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (roundedWorld g) ((P.cap H).worldLaw ν)
      ((P.roundedCap H g hg hgnonneg).worldLaw ν) :=
  (P.roundedValues_measurePreserving H g hg hgnonneg).prod (MeasurePreserving.id _)

lemma capWorld_values_mem (P : Instance n) (H : ℝ≥0) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ ω : World n Seed ∂(P.cap H).worldLaw ν, ∀ i, ω.1 i ∈ Icc (0 : ℝ) H := by
  have hp : MeasurePreserving (fun ω : World n Seed => ω.1) ((P.cap H).worldLaw ν) (P.cap H).valuesLaw :=
    measurePreserving_fst
  have hv : ∀ᵐ x ∂(P.cap H).valuesLaw, ∀ i, x i ∈ Icc (0 : ℝ) H := by
    rw [ae_all_iff]
    intro i
    apply (measurePreserving_eval (P.cap H).law i).quasiMeasurePreserving.ae
    filter_upwards [(P.cap H).nonnegative i, P.cap_bounded H i] with x hx0 hxH
    exact ⟨hx0, hxH⟩
  exact hp.quasiMeasurePreserving.ae hv

lemma expectedMaximum_rounding_bounds (P : Instance n) (H : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g)
    (hgnonneg : ∀ x ∈ Icc (0 : ℝ) H, 0 ≤ g x)
    (hgdown : ∀ x ∈ Icc (0 : ℝ) H, g x ≤ x) {δ : ℝ} (hδ : 0 ≤ δ)
    (herror : ∀ x ∈ Icc (0 : ℝ) H, x - g x ≤ δ) :
    (P.cap H).expectedMaximum - δ ≤ (P.roundedCap H g hg hgnonneg).expectedMaximum ∧
      (P.roundedCap H g hg hgnonneg).expectedMaximum ≤ (P.cap H).expectedMaximum := by
  have hp := P.roundedValues_measurePreserving H g hg hgnonneg
  have hiCap := (P.cap H).integrable_maximum_of_bounded (P.cap_bounded H)
  have hiRound := hp.integrable_comp_of_integrable (P.roundedCap_integrable_maximum H g hg hgnonneg hgdown)
  have hiMap : Integrable (fun x : Fin n → ℝ => maximum (g ∘ x)) (P.cap H).valuesLaw := hiRound
  have hmem : ∀ᵐ x ∂(P.cap H).valuesLaw, ∀ i, x i ∈ Icc (0 : ℝ) H := by
    rw [ae_all_iff]
    intro i
    apply (measurePreserving_eval (P.cap H).law i).quasiMeasurePreserving.ae
    filter_upwards [(P.cap H).nonnegative i, P.cap_bounded H i] with x hx0 hxH
    exact ⟨hx0, hxH⟩
  have hlo := integral_mono_ae hiCap (hiMap.add (integrable_const δ)) (by
    filter_upwards [hmem] with x hx
    apply maximum_le _ (add_nonneg (maximum_nonnegative _) hδ)
    intro i
    have hgi := le_maximum (g ∘ x) i
    have he := herror (x i) (hx i)
    change g (x i) ≤ maximum (g ∘ x) at hgi
    linarith)
  have hhi := integral_mono_ae hiMap hiCap (by
    filter_upwards [hmem] with x hx
    exact maximum_le _ (maximum_nonnegative x) (fun i => (hgdown (x i) (hx i)).trans (le_maximum x i)))
  have he := integral_map (μ := (P.cap H).valuesLaw) hp.measurable.aemeasurable measurable_maximum.aestronglyMeasurable
  rw [hp.map_eq] at he
  change (P.cap H).expectedMaximum ≤ ∫ x : Fin n → ℝ, maximum (g ∘ x) + δ ∂(P.cap H).valuesLaw at hlo
  rw [integral_add hiMap (integrable_const δ), ← he] at hlo
  simp only [integral_const, probReal_univ, one_smul] at hlo
  rw [← he] at hhi
  change (P.cap H).expectedMaximum ≤ (P.roundedCap H g hg hgnonneg).expectedMaximum + δ at hlo
  change (P.roundedCap H g hg hgnonneg).expectedMaximum ≤ (P.cap H).expectedMaximum at hhi
  exact ⟨by linarith, hhi⟩

end Instance
variable [MeasurableSpace Seed]

lemma Policy.reachProbability_rounding_pullback (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (H : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g)
    (hgnonneg : ∀ x ∈ Icc (0 : ℝ) H, 0 ≤ g x) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (π.pullbackValues g).reachProbability (P.cap H) ν i =
      π.reachProbability (P.roundedCap H g hg hgnonneg) ν i := by
  have hp := P.roundedWorld_measurePreserving H g hg hgnonneg ν
  let E : Set (World n Seed) := {ω | π.Reaches ω.2.2 ω.1 ω.2.1 i}
  have hE : MeasurableSet E := π.measurableSet_reaches hπ (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  unfold Policy.reachProbability
  rw [← hp.map_eq, map_measureReal_apply hp.measurable hE]
  congr 1
  ext ω
  simp only [E, Set.mem_preimage, Set.mem_setOf_eq, Policy.Reaches, Instance.roundedWorld,
    π.pullbackValues_stoppingTime]

namespace RandomizedPolicy

lemma roundedReward_le_pullback (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0)
    (g : ℝ → ℝ) (hg : Measurable g) (hgnonneg : ∀ x ∈ Icc (0 : ℝ) H, 0 ≤ g x)
    (hgdown : ∀ x ∈ Icc (0 : ℝ) H, g x ≤ x) :
    π.expectedReward (P.roundedCap H g hg hgnonneg) ≤ (π.pullbackValues g hg).expectedReward (P.cap H) := by
  have hp := P.roundedWorld_measurePreserving H g hg hgnonneg π.seedLaw
  have he := integral_map (μ := (P.cap H).worldLaw π.seedLaw) hp.measurable.aemeasurable
    π.measurable_realizedReward.aestronglyMeasurable
  rw [hp.map_eq] at he
  change ∫ ω, π.realizedReward ω ∂(P.roundedCap H g hg hgnonneg).worldLaw π.seedLaw ≤ _
  rw [he]
  apply integral_mono_ae
    (hp.integrable_comp_of_integrable (π.integrable_realizedReward _ (P.roundedCap_integrable_maximum H g hg hgnonneg hgdown)))
    ((π.pullbackValues g hg).integrable_realizedReward (P.cap H) ((P.cap H).integrable_maximum_of_bounded (P.cap_bounded H)))
  filter_upwards [P.capWorld_values_mem H π.seedLaw] with ω hω
  exact π.rule.reward_display_le_pullback g ω.2.2 ω.1 ω.2.1 (fun i => hgdown (ω.1 i) (hω i))

/-- The cap is kept by rounding, so cap acceptance transfers back to capped displays. -/
lemma pullback_rounding_acceptsCap (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0)
    (g : ℝ → ℝ) (hg : Measurable g) (hgnonneg : ∀ x ∈ Icc (0 : ℝ) H, 0 ≤ g x)
    (hgcap : g H = (H : ℝ))
    (hacc : ∀ᵐ ω : π.World ∂(P.roundedCap H g hg hgnonneg).worldLaw π.seedLaw,
      π.rule.AcceptsReachedCap H ω.2.2 ω.1 ω.2.1) :
    ∀ᵐ ω : π.World ∂(P.cap H).worldLaw π.seedLaw,
      (π.pullbackValues g hg).rule.AcceptsReachedCap H ω.2.2 ω.1 ω.2.1 := by
  have hp := P.roundedWorld_measurePreserving H g hg hgnonneg π.seedLaw
  filter_upwards [hp.quasiMeasurePreserving.ae hacc] with ω hω
  intro i hr hi
  have hr' : π.rule.Reaches ω.2.2 (g ∘ ω.1) ω.2.1 i := by
    simpa only [Policy.Reaches, pullbackValues, Policy.pullbackValues_stoppingTime] using hr
  have hi' : (g ∘ ω.1) i = (H : ℝ) := by simp only [Function.comp_apply, hi, hgcap]
  have ha := hω i hr' hi'
  simpa only [pullbackValues, Policy.pullbackValues_action, Instance.roundedWorld] using ha

/-- The reward inequality in `upouter:lift-identities`, for any fixed downward map
preserving the cap. The extra gain from rounding is kept by the lifted policy. -/
lemma rounded_cap_pullback_tail_gain (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0)
    (hP : Integrable Instance.maximum P.valuesLaw) (g : ℝ → ℝ) (hg : Measurable g)
    (hgnonneg : ∀ x ∈ Icc (0 : ℝ) H, 0 ≤ g x)
    (hgdown : ∀ x ∈ Icc (0 : ℝ) H, g x ≤ x) (hgcap : g H = (H : ℝ))
    (hacc : ∀ᵐ ω : π.World ∂(P.roundedCap H g hg hgnonneg).worldLaw π.seedLaw,
      π.rule.AcceptsReachedCap H ω.2.2 ω.1 ω.2.1) :
    π.expectedReward (P.roundedCap H g hg hgnonneg) +
      ∑ i, π.rule.reachProbability (P.roundedCap H g hg hgnonneg) π.seedLaw i * ∫ x, tailValue H x ∂P.law i ≤
        ((π.pullbackValues g hg).pullbackValues (capValue H) (measurable_capValue H)).expectedReward P := by
  have hacc' := π.pullback_rounding_acceptsCap P H g hg hgnonneg hgcap hacc
  rw [(π.pullbackValues g hg).expectedReward_cap_pullback_eq_tail_gain P H hP hacc']
  have hq : ∀ i, (π.pullbackValues g hg).rule.reachProbability (P.cap H) (π.pullbackValues g hg).seedLaw i =
      π.rule.reachProbability (P.roundedCap H g hg hgnonneg) π.seedLaw i :=
    fun i => π.rule.reachProbability_rounding_pullback π.measurable_rule P H g hg hgnonneg π.seedLaw i
  simp_rw [hq]
  exact add_le_add (π.roundedReward_le_pullback P H g hg hgnonneg hgdown) le_rfl

/-- The complete rounded lifting conclusion. Substituting `δ=H/m` gives
`upouter:lift-conclusion`; no number-of-offers factor occurs in the rounding loss. -/
lemma rounded_cap_pullback_reward_guarantee (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0)
    (hP : Integrable Instance.maximum P.valuesLaw) (g : ℝ → ℝ) (hg : Measurable g)
    (hgnonneg : ∀ x ∈ Icc (0 : ℝ) H, 0 ≤ g x)
    (hgdown : ∀ x ∈ Icc (0 : ℝ) H, g x ≤ x) (hgcap : g H = (H : ℝ))
    {δ : ℝ} (hδ : 0 ≤ δ) (herror : ∀ x ∈ Icc (0 : ℝ) H, x - g x ≤ δ)
    (hacc : ∀ᵐ ω : π.World ∂(P.roundedCap H g hg hgnonneg).worldLaw π.seedLaw,
      π.rule.AcceptsReachedCap H ω.2.2 ω.1 ω.2.1)
    {rho Delta : ℝ} (hrho : 0 ≤ rho)
    (hR : rho * (P.roundedCap H g hg hgnonneg).expectedMaximum - Delta ≤ π.expectedReward (P.roundedCap H g hg hgnonneg))
    (hq : ∀ i, rho ≤ π.rule.reachProbability (P.roundedCap H g hg hgnonneg) π.seedLaw i) :
    rho * P.expectedMaximum - Delta - rho * δ ≤
      ((π.pullbackValues g hg).pullbackValues (capValue H) (measurable_capValue H)).expectedReward P := by
  have htail : rho * P.tailSum H ≤
      ∑ i, π.rule.reachProbability (P.roundedCap H g hg hgnonneg) π.seedLaw i * ∫ x, tailValue H x ∂P.law i := by
    rw [Instance.tailSum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hq i)
      (integral_nonneg fun x => tailValue_nonnegative H x)
  have hmax0 := P.expectedMaximum_le_cap_add_tailSum H hP
  have hmax1 := (P.expectedMaximum_rounding_bounds H g hg hgnonneg hgdown hδ herror).1
  have hmax : P.expectedMaximum ≤ (P.roundedCap H g hg hgnonneg).expectedMaximum + δ + P.tailSum H := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hmax hrho
  have hgain := π.rounded_cap_pullback_tail_gain P H hP g hg hgnonneg hgdown hgcap hacc
  nlinarith

end RandomizedPolicy

end ProphetSecretary.Model
