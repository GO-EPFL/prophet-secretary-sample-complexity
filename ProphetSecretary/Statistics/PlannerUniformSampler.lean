import ProphetSecretary.Statistics.PlannerFirstSuccess
import ProphetSecretary.Statistics.PlannerTransitionLaw
import ProphetSecretary.Probability.UniformSubsetMaximum
import ProphetSecretary.Model.TrainingMeasurability

/-!
# A fixed uniform seed for the planner transition

The seed has two scalar uniforms and three independent finite uniform
reservoirs. Neither its type nor its law depends on the active state or its
positive probabilities. Empty states have an explicit option-valued output.
-/

open MeasureTheory Set Filter
open scoped Classical ENNReal BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def plannerUniformIdentity {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty)
    (u : ℝ) : Fin n := categoricalUniformSample D hD (fun _ => 1 / (D.card : ℝ)) u

lemma measurable_plannerUniformIdentity {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty) :
    Measurable (plannerUniformIdentity D hD) := measurable_categoricalUniformSample D hD _

lemma map_plannerUniformIdentity {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty) :
    Instance.uniformClock.map (plannerUniformIdentity D hD) = (PMF.uniformOfFinset D hD).toMeasure := by
  apply map_categoricalUniformSample_eq_pmf D hD (fun _ => 1 / (D.card : ℝ))
  · intro i _
    positivity
  · simp only [Finset.sum_const, nsmul_eq_mul]
    have hc : (D.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hD).ne'
    field_simp
  · intro i
    rw [PMF.uniformOfFinset_apply]
    have hc : 0 < (D.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hD)
    rw [one_div, ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast]
    by_cases hi : i ∈ D <;> simp [hi]

/-- Totalized unit-interval maximum; clipping changes only null seed inputs. -/
noncomputable def plannerUnitFraction {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty)
    (u : Fin n → ℝ) : ℝ := max 0 (min (uniformSubsetMaximum D hD u) 1)

lemma measurable_plannerUnitFraction {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty) :
    Measurable (plannerUnitFraction D hD) :=
  measurable_const.max ((measurable_uniformSubsetMaximum D hD).min measurable_const)

lemma plannerUnitFraction_mem_unit {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty)
    (u : Fin n → ℝ) : plannerUnitFraction D hD u ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

lemma map_plannerUnitFraction {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty) :
    (Instance.clocksLaw n).map (plannerUnitFraction D hD) =
      (Instance.clocksLaw D.card).map
        (uniformMaximum D.card (Nat.succ_le_of_lt (Finset.card_pos.mpr hD))) := by
  have hEq : plannerUnitFraction D hD =ᵐ[Instance.clocksLaw n] uniformSubsetMaximum D hD := by
    filter_upwards [Instance.clocks_mem_unitInterval (n := n)] with u hu
    let i := Classical.choose hD
    have hi : i ∈ D := Classical.choose_spec hD
    have h0 : 0 ≤ uniformSubsetMaximum D hD u := (hu i).1.trans (Finset.le_sup' u hi)
    have h1 : uniformSubsetMaximum D hD u ≤ 1 := Finset.sup'_le hD u (fun j _ => (hu j).2)
    unfold plannerUnitFraction
    rw [min_eq_left h1, max_eq_right h0]
  exact (Measure.map_congr hEq).trans (map_uniformSubsetMaximum_eq_uniformMaximum D hD)

noncomputable def plannerMaskedTransition {n : ℕ} (A D : Finset (Fin n)) (hD : D.Nonempty)
    (i : Fin n) (seed : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n × ℝ × Finset (Fin n) :=
  let s := plannerUnitFraction D hD seed.1
  (i, s, plannerTailSet A D i s seed.2)

lemma measurable_plannerMaskedTransition {n : ℕ} (A D : Finset (Fin n)) (hD : D.Nonempty)
    (i : Fin n) : Measurable (plannerMaskedTransition A D hD i) := by
  have hmax : Measurable (fun a : (Fin n → ℝ) × (Fin n → ℝ) => plannerUnitFraction D hD a.1) :=
    (measurable_plannerUnitFraction D hD).comp measurable_fst
  exact measurable_const.prodMk (hmax.prodMk (measurable_plannerTailSet A D i _ _ hmax
    (fun j => (measurable_pi_apply j).comp measurable_snd)))

lemma map_plannerMaskedTransition {n : ℕ} (A D : Finset (Fin n)) (hD : D.Nonempty) (i : Fin n) :
    ((Instance.clocksLaw n).prod (Instance.clocksLaw n)).map (plannerMaskedTransition A D hD i) =
      plannerConditionalTransitionLaw A D hD i := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hTail : Measurable (fun q : ℝ × (Fin n → ℝ) => f (i, q.1, plannerTailSet A D i q.1 q.2)) :=
    hf.comp (measurable_const.prodMk (measurable_fst.prodMk
      (measurable_plannerTailSet A D i _ _ measurable_fst
        (fun j => (measurable_pi_apply j).comp measurable_snd))))
  let G : ℝ → ℝ≥0∞ := fun s => ∫⁻ u, f (i, s, plannerTailSet A D i s u) ∂Instance.clocksLaw n
  have hG : Measurable G := hTail.lintegral_prod_right'
  rw [lintegral_map hf (measurable_plannerMaskedTransition A D hD i),
    plannerConditionalTransitionLaw,
    lintegral_map hf (measurable_plannerConditionalTransition A D hD i)]
  change (∫⁻ a, (f ∘ plannerMaskedTransition A D hD i) a
      ∂(Instance.clocksLaw n).prod (Instance.clocksLaw n)) =
    ∫⁻ a, (f ∘ plannerConditionalTransition A D hD i) a
      ∂(Instance.clocksLaw D.card).prod (Instance.clocksLaw n)
  rw [lintegral_prod _ (hf.comp (measurable_plannerMaskedTransition A D hD i)).aemeasurable,
    lintegral_prod _ (hf.comp (measurable_plannerConditionalTransition A D hD i)).aemeasurable]
  change (∫⁻ a, G (plannerUnitFraction D hD a) ∂Instance.clocksLaw n) =
    ∫⁻ a, G (uniformMaximum D.card (Nat.succ_le_of_lt (Finset.card_pos.mpr hD)) a)
      ∂Instance.clocksLaw D.card
  rw [← lintegral_map hG (measurable_plannerUnitFraction D hD),
    map_plannerUnitFraction,
    lintegral_map hG (measurable_uniformMaximum D.card _)]

abbrev PlannerUniformTailSeed (n : ℕ) := ℝ × ((Fin n → ℝ) × (Fin n → ℝ))

noncomputable def plannerUniformTailSeedLaw (n : ℕ) : Measure (PlannerUniformTailSeed n) :=
  Instance.uniformClock.prod ((Instance.clocksLaw n).prod (Instance.clocksLaw n))

instance plannerUniformTailSeedLaw_probability (n : ℕ) : IsProbabilityMeasure (plannerUniformTailSeedLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Instance.uniformClock.prod
    ((Instance.clocksLaw n).prod (Instance.clocksLaw n))))

noncomputable def plannerUniformIdentityTransition {n : ℕ} (A D : Finset (Fin n)) (hD : D.Nonempty)
    (seed : PlannerUniformTailSeed n) : Fin n × ℝ × Finset (Fin n) :=
  plannerMaskedTransition A D hD (plannerUniformIdentity D hD seed.1) seed.2

lemma measurable_plannerUniformIdentityTransition {n : ℕ} (A D : Finset (Fin n)) (hD : D.Nonempty) :
    Measurable (plannerUniformIdentityTransition A D hD) := by
  have hJoint : Measurable (fun z : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      plannerMaskedTransition A D hD z.1 z.2) :=
    measurable_from_prod_countable_right (fun i => measurable_plannerMaskedTransition A D hD i)
  exact hJoint.comp (((measurable_plannerUniformIdentity D hD).comp measurable_fst).prodMk measurable_snd)

lemma map_plannerUniformIdentityTransition {n : ℕ} (A D : Finset (Fin n)) (hD : D.Nonempty) :
    (plannerUniformTailSeedLaw n).map (plannerUniformIdentityTransition A D hD) =
      plannerIdentityTransitionLaw A D := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_plannerUniformIdentityTransition A D hD)]
  change (∫⁻ a, (f ∘ plannerUniformIdentityTransition A D hD) a
      ∂Instance.uniformClock.prod ((Instance.clocksLaw n).prod (Instance.clocksLaw n))) = _
  rw [lintegral_prod _ (hf.comp (measurable_plannerUniformIdentityTransition A D hD)).aemeasurable,
    plannerIdentityTransitionLaw, dif_pos hD,
    Measure.lintegral_bind (measurable_of_countable _).aemeasurable hf.aemeasurable]
  have hEach (i : Fin n) : (∫⁻ x, f x ∂plannerConditionalTransitionLaw A D hD i) =
      ∫⁻ a, f (plannerMaskedTransition A D hD i a)
        ∂(Instance.clocksLaw n).prod (Instance.clocksLaw n) := by
    rw [← map_plannerMaskedTransition A D hD i,
      lintegral_map hf (measurable_plannerMaskedTransition A D hD i)]
  simp_rw [hEach]
  rw [← map_plannerUniformIdentity D hD]
  exact (lintegral_map (measurable_of_countable (fun i => ∫⁻ a,
    f (plannerMaskedTransition A D hD i a) ∂(Instance.clocksLaw n).prod (Instance.clocksLaw n)))
      (measurable_plannerUniformIdentity D hD)).symm

abbrev PlannerUniformSeed (n : ℕ) := (ℝ × (Fin n → ℝ)) × PlannerUniformTailSeed n
abbrev PlannerUniformOutput (n : ℕ) := Option (Fin n) × ℝ × Finset (Fin n)

noncomputable def plannerUniformSeedLaw (n : ℕ) : Measure (PlannerUniformSeed n) :=
  (Instance.uniformClock.prod (Instance.clocksLaw n)).prod (plannerUniformTailSeedLaw n)

instance plannerUniformSeedLaw_probability (n : ℕ) : IsProbabilityMeasure (plannerUniformSeedLaw n) :=
  inferInstanceAs (IsProbabilityMeasure ((Instance.uniformClock.prod (Instance.clocksLaw n)).prod
    (plannerUniformTailSeedLaw n)))

def plannerSomeTransition {n : ℕ} (x : Fin n × ℝ × Finset (Fin n)) : PlannerUniformOutput n :=
  (some x.1, x.2)

lemma measurable_plannerSomeTransition (n : ℕ) : Measurable (@plannerSomeTransition n) :=
  ((measurable_of_countable (fun i : Fin n => some i)).comp measurable_fst).prodMk measurable_snd

noncomputable def plannerUniformAfterSubset {n : ℕ} (A D : Finset (Fin n))
    (seed : PlannerUniformTailSeed n) : PlannerUniformOutput n :=
  if hD : D.Nonempty then plannerSomeTransition (plannerUniformIdentityTransition A D hD seed)
  else (none, 0, ∅)

lemma measurable_plannerUniformAfterSubset {n : ℕ} (A D : Finset (Fin n)) :
    Measurable (plannerUniformAfterSubset A D) := by
  unfold plannerUniformAfterSubset
  split_ifs with hD
  · exact (measurable_plannerSomeTransition n).comp (measurable_plannerUniformIdentityTransition A D hD)
  · exact measurable_const

noncomputable def plannerUniformTransition {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (seed : PlannerUniformSeed n) : PlannerUniformOutput n :=
  if hA : A.Nonempty then
    plannerUniformAfterSubset A (plannerFirstSuccessUniform A p hA seed.1) seed.2
  else (none, 0, ∅)

lemma measurable_plannerUniformTransition {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ) :
    Measurable (plannerUniformTransition A p) := by
  unfold plannerUniformTransition
  split_ifs with hA
  · have hJoint : Measurable (fun z : Finset (Fin n) × PlannerUniformTailSeed n =>
        plannerUniformAfterSubset A z.1 z.2) :=
      measurable_from_prod_countable_right (fun D => measurable_plannerUniformAfterSubset A D)
    exact hJoint.comp (((measurable_plannerFirstSuccessUniform A p hA).comp measurable_fst).prodMk measurable_snd)
  · exact measurable_const

lemma plannerUniformTransition_empty {n : ℕ} (p : Fin n → ℝ) (seed : PlannerUniformSeed n) :
    plannerUniformTransition ∅ p seed = (none, 0, ∅) := by
  simp [plannerUniformTransition]

/-- The complete sampler uses one seed law for every active set and probability
vector. Its nonempty-state law is exactly the prescribed planner kernel. -/
theorem map_plannerUniformTransition_of_nonempty {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    (plannerUniformSeedLaw n).map (plannerUniformTransition A p) =
      (plannerKernelLaw A p).map plannerSomeTransition := by
  apply Measure.ext_of_lintegral
  intro f hf
  let H : Finset (Fin n) → ℝ≥0∞ := fun D =>
    ∫⁻ seed, f (plannerUniformAfterSubset A D seed) ∂plannerUniformTailSeedLaw n
  have hH : Measurable H := measurable_of_countable _
  rw [lintegral_map hf (measurable_plannerUniformTransition A p),
    lintegral_map hf (measurable_plannerSomeTransition n)]
  change (∫⁻ seed, (f ∘ plannerUniformTransition A p) seed
      ∂(Instance.uniformClock.prod (Instance.clocksLaw n)).prod (plannerUniformTailSeedLaw n)) = _
  rw [lintegral_prod _ (hf.comp (measurable_plannerUniformTransition A p)).aemeasurable]
  simp only [Function.comp_apply, plannerUniformTransition, dif_pos hA]
  change (∫⁻ seed, H (plannerFirstSuccessUniform A p hA seed)
      ∂Instance.uniformClock.prod (Instance.clocksLaw n)) = _
  rw [← lintegral_map hH (measurable_plannerFirstSuccessUniform A p hA),
    map_plannerFirstSuccessUniform A p hA hp,
    ← plannerTransitionLaw_eq_kernelLaw A p hA hp, plannerTransitionLaw]
  change (∫⁻ D, H D ∂(plannerNonemptySubsetPMF A p hA hp).toMeasure) =
    ∫⁻ x, (f ∘ plannerSomeTransition) x
      ∂(plannerNonemptySubsetPMF A p hA hp).toMeasure.bind (plannerIdentityTransitionLaw A)
  rw [Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (hf.comp (measurable_plannerSomeTransition n)).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [plannerNonemptySubsetPMF_ae_nonempty A p hA hp] with D hD
  dsimp only [H]
  simp only [plannerUniformAfterSubset, dif_pos hD]
  rw [← map_plannerUniformIdentityTransition A D hD,
    lintegral_map (hf.comp (measurable_plannerSomeTransition n))
      (measurable_plannerUniformIdentityTransition A D hD)]
  rfl

/-- Empty states, including the zero-dimensional instance, return a fixed
option-valued output and do not require an identity choice. -/
theorem map_plannerUniformTransition_empty (n : ℕ) (p : Fin n → ℝ) :
    (plannerUniformSeedLaw n).map (plannerUniformTransition ∅ p) =
      Measure.dirac (none, 0, ∅) := by
  have he : plannerUniformTransition ∅ p = fun _ : PlannerUniformSeed n =>
      ((none, 0, ∅) : PlannerUniformOutput n) := by
    funext seed
    exact plannerUniformTransition_empty p seed
  rw [he, Measure.map_const]
  simp

/-- Number of uniform coordinates read: first-success choice and later
coins, identity choice, masked maximum, and the additional tail coins. -/
noncomputable def plannerUniformReadCount {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (seed : PlannerUniformSeed n) : ℕ :=
  if hA : A.Nonempty then
    let k := plannerFirstSuccessChoice A p hA seed.1.1
    let D := plannerFirstSuccessUniform A p hA seed.1
    2 + (A.filter (fun j => k < j)).card + D.card + (A \ D).card
  else 0

/-- The number of random draws is linear in the active size on every raw
seed, without rejection sampling or a high-probability work cutoff. -/
theorem plannerUniformReadCount_le {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (seed : PlannerUniformSeed n) : plannerUniformReadCount A p seed ≤ 2 * A.card + 2 := by
  by_cases hA : A.Nonempty
  · have hD := plannerFirstSuccessUniform_subset A p hA seed.1
    have hCard := Finset.card_sdiff_add_card_eq_card hD
    have hLater := Finset.card_le_card (Finset.filter_subset
      (fun j => plannerFirstSuccessChoice A p hA seed.1.1 < j) A)
    unfold plannerUniformReadCount
    rw [dif_pos hA]
    dsimp only
    omega
  · simp only [plannerUniformReadCount, dif_neg hA]
    omega

@[simp] lemma plannerUniformReadCount_empty {n : ℕ} (p : Fin n → ℝ) (seed : PlannerUniformSeed n) :
    plannerUniformReadCount ∅ p seed = 0 := by
  simp [plannerUniformReadCount]

/-- Unread uniform coordinates do not affect the transition. -/
lemma plannerUniformTransition_eq_of_seed_agrees {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (seed seed' : PlannerUniformSeed n)
    (hFirst : seed.1.1 = seed'.1.1) (hIdentity : seed.2.1 = seed'.2.1)
    (hFirstCoins : ∀ j ∈ A.filter (fun j => plannerFirstSuccessChoice A p hA seed.1.1 < j),
      seed.1.2 j = seed'.1.2 j)
    (hMax : ∀ j ∈ plannerFirstSuccessUniform A p hA seed.1, seed.2.2.1 j = seed'.2.2.1 j)
    (hTail : ∀ j ∈ A \ plannerFirstSuccessUniform A p hA seed.1, seed.2.2.2 j = seed'.2.2.2 j) :
    plannerUniformTransition A p seed = plannerUniformTransition A p seed' := by
  have hK : plannerFirstSuccessChoice A p hA seed.1.1 =
      plannerFirstSuccessChoice A p hA seed'.1.1 := congrArg _ hFirst
  have hCoins : bernoulliSubset (A.filter (fun j => plannerFirstSuccessChoice A p hA seed.1.1 < j))
      (fun j => plannerBernoulliProbability (p j)) seed.1.2 =
      bernoulliSubset (A.filter (fun j => plannerFirstSuccessChoice A p hA seed.1.1 < j))
        (fun j => plannerBernoulliProbability (p j)) seed'.1.2 := by
    apply Finset.filter_congr
    intro j hj
    rw [hFirstCoins j hj]
  have hD : plannerFirstSuccessUniform A p hA seed.1 = plannerFirstSuccessUniform A p hA seed'.1 := by
    unfold plannerFirstSuccessUniform plannerFirstSuccessSet
    rw [← hK, hCoins]
  let D := plannerFirstSuccessUniform A p hA seed.1
  have hDne : D.Nonempty := plannerFirstSuccessUniform_nonempty A p hA seed.1
  have hMaxEq : plannerUnitFraction D hDne seed.2.2.1 = plannerUnitFraction D hDne seed'.2.2.1 := by
    unfold plannerUnitFraction uniformSubsetMaximum
    rw [Finset.sup'_congr hDne rfl (fun j hj => hMax j hj)]
  have hTailEq : ∀ s : ℝ, bernoulliSubset (A \ D) (fun _ => s) seed.2.2.2 =
      bernoulliSubset (A \ D) (fun _ => s) seed'.2.2.2 := by
    intro s
    apply Finset.filter_congr
    intro j hj
    rw [hTail j hj]
  simp only [plannerUniformTransition, dif_pos hA]
  rw [← hD]
  change plannerUniformAfterSubset A D seed.2 = plannerUniformAfterSubset A D seed'.2
  simp only [plannerUniformAfterSubset, dif_pos hDne, plannerUniformIdentityTransition,
    plannerMaskedTransition, plannerSomeTransition]
  rw [hIdentity, hMaxEq]
  simp only [plannerTailSet, hTailEq]

/-- Every raw seed produces a legal smaller state, including seeds outside
the support of the probability law. -/
lemma plannerUniformTransition_legal {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (seed : PlannerUniformSeed n) {i : Fin n} (hSelect : (plannerUniformTransition A p seed).1 = some i) :
    i ∈ A ∧ (plannerUniformTransition A p seed).2.1 ∈ Icc (0 : ℝ) 1 ∧
      (plannerUniformTransition A p seed).2.2 ⊆ A.erase i := by
  by_cases hA : A.Nonempty
  · let D := plannerFirstSuccessUniform A p hA seed.1
    have hD : D.Nonempty := plannerFirstSuccessUniform_nonempty A p hA seed.1
    have hDA : D ⊆ A := plannerFirstSuccessUniform_subset A p hA seed.1
    let j := plannerUniformIdentity D hD seed.2.1
    have hj : j ∈ D := categoricalUniformSample_mem D hD _ _
    let s := plannerUnitFraction D hD seed.2.2.1
    have hOut : plannerUniformTransition A p seed =
        (some j, s, plannerTailSet A D j s seed.2.2.2) := by
      unfold plannerUniformTransition
      rw [dif_pos hA]
      change plannerUniformAfterSubset A D seed.2 = _
      rw [plannerUniformAfterSubset, dif_pos hD]
      rfl
    rw [hOut] at hSelect
    have hji : j = i := Option.some.inj hSelect
    subst i
    rw [hOut]
    refine ⟨hDA hj, plannerUnitFraction_mem_unit D hD _, ?_⟩
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · have h := Finset.mem_erase.mp hk
      exact Finset.mem_erase.mpr ⟨h.1, hDA h.2⟩
    · have h := Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1
      exact Finset.mem_erase.mpr ⟨fun hkj => h.2 (hkj ▸ hj), h.1⟩
  · simp only [plannerUniformTransition, dif_neg hA] at hSelect
    contradiction

lemma plannerUniformTransition_child_card_lt {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (seed : PlannerUniformSeed n) {i : Fin n} (hSelect : (plannerUniformTransition A p seed).1 = some i) :
    (plannerUniformTransition A p seed).2.2.card < A.card := by
  have h := plannerUniformTransition_legal A p seed hSelect
  have hc := Finset.card_le_card h.2.2
  have he := Finset.card_erase_of_mem h.1
  have hPos : 0 < A.card := Finset.card_pos.mpr ⟨i, h.1⟩
  omega

end ProphetSecretary.Statistics
