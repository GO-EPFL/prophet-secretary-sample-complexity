import ProphetSecretary.Model.SurvivalComparison
import Mathlib.Probability.Independence.Integration

/-!
# Survival allocation at deterministic time

Observable prefix survival is independent of the rescaled unseen block by explicit
product-law factorization. Multiplying the pathwise canonical-child comparison by a
nonnegative prefix statistic therefore allocates its actual expected child duration.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma splitClocks_mem_unitInterval (A : Finset (Fin n)) (i : Fin n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (v : Fin n → ℝ) (hv : ∀ j, v j ∈ Icc (0 : ℝ) 1) :
    ∀ j, splitClocks A i t v j ∈ Icc (0 : ℝ) 1 := by
  intro j
  simp only [splitClocks, splitClock]
  split_ifs with hji hjA
  · exact hv j
  · unfold Instance.tailClock
    constructor <;> nlinarith [(hv j).1, (hv j).2]
  · constructor <;> nlinarith [(hv j).1, (hv j).2]

omit [MeasurableSpace Seed] in
lemma survivingPrefixWeight_bounds (π : Policy Seed n) (W : Seed × History n → ℝ)
    {K : ℝ} (hW : ∀ z, 0 ≤ W z ∧ W z ≤ K)
    (A : Finset (Fin n)) (i : Fin n) (t : ℝ) (ω : World n Seed) :
    0 ≤ survivingPrefixWeight π W A i t ω ∧ survivingPrefixWeight π W A i t ω ≤ K := by
  have hK : 0 ≤ K := (hW (ω.2.2, observedPrefix i t (splitWorld A i t ω))).1.trans
    (hW (ω.2.2, observedPrefix i t (splitWorld A i t ω))).2
  unfold survivingPrefixWeight
  split_ifs
  · simpa only [mul_one] using hW (ω.2.2, observedPrefix i t (splitWorld A i t ω))
  · simpa only [mul_zero] using And.intro (le_refl (0 : ℝ)) hK

/-- The deterministic-time allocation inequality under the explicit state coupling.
The multiplier sees the observed prefix, including zero identities, and an arbitrary
independent auxiliary seed. It does not see the fresh values or arrival clocks. -/
lemma Instance.survival_allocation_split (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A)
    {w c t K : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (ht0 : 0 < t) (ht1 : t < 1)
    (W : Seed × History n → ℝ) (hW : Measurable W) (hWbounds : ∀ z, 0 ≤ W z ∧ W z ≤ K) :
    let π := (P.valuePolicy hP hw.le hc).rule.withAuxiliarySeed (Seed := Seed)
    let ψ := (P.restrictTo A).valuePolicy (P.restrictTo_integrable_maximum A hP)
      hw.le (mul_nonneg hc (sub_nonneg.mpr ht1.le))
    let F := survivingPrefixWeight π W A i t
    (1 - t) * ψ.expectedDuration (P.restrictTo A) * (∫ ω, F ω ∂P.worldLaw ν) ≤
      ∫ ω, F ω * (π.pendingTime ω.2.2 (splitWorld A i t ω).1 (splitWorld A i t ω).2.1 i - t) ∂P.worldLaw ν := by
  let π := (P.valuePolicy hP hw.le hc).rule.withAuxiliarySeed (Seed := Seed)
  let ψ := (P.restrictTo A).valuePolicy (P.restrictTo_integrable_maximum A hP)
    hw.le (mul_nonneg hc (sub_nonneg.mpr ht1.le))
  let F := survivingPrefixWeight π W A i t
  let D := fun ω : World n Seed => ψ.realizedDuration (freshWorld A ω)
  let σ := fun ω : World n Seed => π.pendingTime ω.2.2 (splitWorld A i t ω).1 (splitWorld A i t ω).2.1 i
  change (1 - t) * ψ.expectedDuration (P.restrictTo A) * (∫ ω, F ω ∂P.worldLaw ν) ≤
    ∫ ω, F ω * (σ ω - t) ∂P.worldLaw ν
  have hπ : π.IsMeasurable := (P.valuePolicy hP hw.le hc).rule.withAuxiliarySeed_isMeasurable (P.valuePolicy hP hw.le hc).measurable_rule
  have hF : Measurable F := measurable_survivingPrefixWeight π hπ W hW A i t
  have hD : Measurable D := ψ.measurable_realizedDuration.comp (measurable_freshWorld A)
  have hσ : Measurable σ := (π.measurable_pendingWorldTime hπ i).comp (measurable_splitWorld A i t)
  have hFb : ∀ ω, 0 ≤ F ω ∧ F ω ≤ K := survivingPrefixWeight_bounds π W hWbounds A i t
  have hFnorm : ∀ᵐ ω ∂P.worldLaw ν, ‖F ω‖ ≤ K := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hFb ω).1]
    exact (hFb ω).2
  have hFi : Integrable F (P.worldLaw ν) := Integrable.of_bound hF.aestronglyMeasurable K hFnorm
  have hDi : Integrable D (P.worldLaw ν) :=
    (P.freshWorld_measurePreserving ν A).integrable_comp_of_integrable (ψ.integrable_realizedDuration (P.restrictTo A))
  have hσb : ∀ᵐ ω ∂P.worldLaw ν, σ ω ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [P.world_clocks_mem_unitInterval ν] with ω hω
    have hv := splitClocks_mem_unitInterval A i ht0.le ht1.le ω.2.1 hω
    exact ⟨π.stoppingTime_nonneg _ _ _ _ (fun j => (hv j).1), π.stoppingTime_le_one _ _ _ _⟩
  have hσi : Integrable σ (P.worldLaw ν) := Integrable.of_bound hσ.aestronglyMeasurable 1 (by
    filter_upwards [hσb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
    exact hω.2)
  have hlefti : Integrable (fun ω => F ω * ((1 - t) * D ω)) (P.worldLaw ν) :=
    (hDi.const_mul (1 - t)).bdd_mul hF.aestronglyMeasurable hFnorm
  have hrighti : Integrable (fun ω => F ω * (σ ω - t)) (P.worldLaw ν) :=
    (hσi.sub (integrable_const t)).bdd_mul hF.aestronglyMeasurable hFnorm
  have hlt : ∀ᵐ ω : World n Seed ∂P.worldLaw ν, ∀ j, ω.2.1 j < 1 := by
    have hne : ∀ᵐ ω : World n Seed ∂P.worldLaw ν, ∀ j, ω.2.1 j ≠ 1 :=
      ae_all_iff.mpr fun j => (P.world_clock_measurePreserving ν j).quasiMeasurePreserving.ae (Instance.uniformClock.ae_ne 1)
    filter_upwards [P.world_clocks_mem_unitInterval ν, hne] with ω hω hn
    intro j
    exact lt_of_le_of_ne (hω j).2 (hn j)
  have hpath : ∀ᵐ ω ∂P.worldLaw ν, F ω * ((1 - t) * D ω) ≤ F ω * (σ ω - t) := by
    filter_upwards [hlt] with ω hv
    by_cases hs : t ≤ σ ω
    · have hp := P.pendingTime_ge_rescaled_child hP A i hAi hw hc ht0 ht1 ω.1 ω.2.1 hv hs
      change t + (1 - t) * D ω ≤ σ ω at hp
      have hd : (1 - t) * D ω ≤ σ ω - t := by linarith
      exact mul_le_mul_of_nonneg_left hd (hFb ω).1
    · have hfzero : F ω = 0 := by
        change W (ω.2.2, observedPrefix i t (splitWorld A i t ω)) * (if t ≤ σ ω then 1 else 0) = 0
        rw [if_neg hs, mul_zero]
      rw [hfzero, zero_mul, zero_mul]
  have hind := (P.survivingPrefixWeight_fresh_independent ν π hπ W hW A i hAi ht1.le).comp
    measurable_id ψ.measurable_realizedDuration
  have hmul : (∫ ω, F ω * D ω ∂P.worldLaw ν) = (∫ ω, F ω ∂P.worldLaw ν) * ∫ ω, D ω ∂P.worldLaw ν :=
    hind.integral_fun_mul_eq_mul_integral hF.aestronglyMeasurable hD.aestronglyMeasurable
  have hDmean : (∫ ω, D ω ∂P.worldLaw ν) = ψ.expectedDuration (P.restrictTo A) := by
    have hm := integral_map (μ := P.worldLaw ν) (P.freshWorld_measurePreserving ν A).measurable.aemeasurable
      ψ.measurable_realizedDuration.aestronglyMeasurable
    rw [(P.freshWorld_measurePreserving ν A).map_eq] at hm
    exact hm.symm
  have hmean := integral_mono_ae hlefti hrighti hpath
  have hleft : (∫ ω, F ω * ((1 - t) * D ω) ∂P.worldLaw ν) =
      (1 - t) * ψ.expectedDuration (P.restrictTo A) * ∫ ω, F ω ∂P.worldLaw ν := by
    calc
      _ = (1 - t) * ∫ ω, F ω * D ω ∂P.worldLaw ν := by
        rw [← integral_const_mul]
        congr 1
        funext ω
        ring
      _ = _ := by rw [hmul, hDmean]; ring
  rwa [hleft] at hmean

/-- Prefix weight on the original execution. Its indicator is the analytically
constructed pending execution's survival event. -/
noncomputable def prefixSurvivalWeight (π : Policy Seed n) (W : Seed × History n → ℝ)
    (i : Fin n) (t : ℝ) (ω : World n Seed) : ℝ :=
  W (ω.2.2, observedPrefix i t ω) * (if t ≤ π.pendingTime ω.2.2 ω.1 ω.2.1 i then 1 else 0)

lemma measurable_prefixSurvivalWeight (π : Policy Seed n) (hπ : π.IsMeasurable)
    (W : Seed × History n → ℝ) (hW : Measurable W) (i : Fin n) (t : ℝ) :
    Measurable (prefixSurvivalWeight π W i t) := by
  have hw := hW.comp ((measurable_snd.comp measurable_snd).prodMk (measurable_observedPrefix i t))
  exact hw.mul (Measurable.ite (measurableSet_le measurable_const (π.measurable_pendingWorldTime hπ i))
    measurable_const measurable_const)

/-- The explicit state law transports integrals without division by a state
probability, so null unseen states cause no exceptional conditional definitions. -/
lemma Instance.integral_state_split (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (f : World n Seed → ℝ) (hf : Measurable f) :
    (∫ ω in {ω : World n Seed | otherUnseen ω.2.1 i t = A}, f ω ∂P.worldLaw ν) =
      (clockStateMass A i t).toReal * ∫ ω, f (splitWorld A i t ω) ∂P.worldLaw ν := by
  rw [P.worldLaw_restrict_state ν A i hAi ht0 ht1, integral_smul_measure]
  congr 1
  exact integral_map (measurable_splitWorld A i t).aemeasurable hf.aestronglyMeasurable

/-- `eq:ps-survival-allocation`, integrated on a fixed deterministic unseen state.
Every multiplier is a nonnegative bounded function of the observed prefix and
independent auxiliary randomness; all fresh coordinates are integrated with their
proved product law. The actual canonical child duration includes terminal time one. -/
lemma Instance.survival_allocation (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A)
    {w c t K : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (ht0 : 0 < t) (ht1 : t < 1)
    (W : Seed × History n → ℝ) (hW : Measurable W) (hWbounds : ∀ z, 0 ≤ W z ∧ W z ≤ K) :
    let π := (P.valuePolicy hP hw.le hc).rule.withAuxiliarySeed (Seed := Seed)
    let ψ := (P.restrictTo A).valuePolicy (P.restrictTo_integrable_maximum A hP)
      hw.le (mul_nonneg hc (sub_nonneg.mpr ht1.le))
    let G := prefixSurvivalWeight π W i t
    (1 - t) * ψ.expectedDuration (P.restrictTo A) *
      (∫ ω in {ω : World n Seed | otherUnseen ω.2.1 i t = A}, G ω ∂P.worldLaw ν) ≤
      ∫ ω in {ω : World n Seed | otherUnseen ω.2.1 i t = A},
        G ω * (π.pendingTime ω.2.2 ω.1 ω.2.1 i - t) ∂P.worldLaw ν := by
  let π := (P.valuePolicy hP hw.le hc).rule.withAuxiliarySeed (Seed := Seed)
  let ψ := (P.restrictTo A).valuePolicy (P.restrictTo_integrable_maximum A hP)
    hw.le (mul_nonneg hc (sub_nonneg.mpr ht1.le))
  let G := prefixSurvivalWeight π W i t
  let F := survivingPrefixWeight π W A i t
  let σ := fun ω : World n Seed => π.pendingTime ω.2.2 (splitWorld A i t ω).1 (splitWorld A i t ω).2.1 i
  have hπ : π.IsMeasurable := (P.valuePolicy hP hw.le hc).rule.withAuxiliarySeed_isMeasurable (P.valuePolicy hP hw.le hc).measurable_rule
  have hG : Measurable G := measurable_prefixSurvivalWeight π hπ W hW i t
  have hσ := π.measurable_pendingWorldTime hπ i
  have hGint := P.integral_state_split ν A i hAi ht0 ht1 G hG
  have hprodint := P.integral_state_split ν A i hAi ht0 ht1
    (fun ω => G ω * (π.pendingTime ω.2.2 ω.1 ω.2.1 i - t)) (hG.mul (hσ.sub measurable_const))
  have hsplit := P.survival_allocation_split hP ν A i hAi hw hc ht0 ht1 W hW hWbounds
  change (1 - t) * ψ.expectedDuration (P.restrictTo A) * (∫ ω, F ω ∂P.worldLaw ν) ≤
    ∫ ω, F ω * (σ ω - t) ∂P.worldLaw ν at hsplit
  change (1 - t) * ψ.expectedDuration (P.restrictTo A) *
    (∫ ω in {ω : World n Seed | otherUnseen ω.2.1 i t = A}, G ω ∂P.worldLaw ν) ≤ _
  calc
    _ = (clockStateMass A i t).toReal *
        ((1 - t) * ψ.expectedDuration (P.restrictTo A) * ∫ ω, F ω ∂P.worldLaw ν) := by
      rw [hGint]
      change _ = (clockStateMass A i t).toReal *
        ((1 - t) * ψ.expectedDuration (P.restrictTo A) * ∫ ω, G (splitWorld A i t ω) ∂P.worldLaw ν)
      ring
    _ ≤ (clockStateMass A i t).toReal * (∫ ω, F ω * (σ ω - t) ∂P.worldLaw ν) :=
      mul_le_mul_of_nonneg_left hsplit ENNReal.toReal_nonneg
    _ = _ := hprodint.symm

omit [MeasurableSpace Seed] in
lemma survival_duration_integral {t σ : ℝ} (htσ : t ≤ σ) (hσ1 : σ ≤ 1) :
    (∫ s in Icc t (1 : ℝ), (if s ≤ σ then (1 : ℝ) else 0)) = σ - t := by
  have he : (Icc t (1 : ℝ)).indicator (fun s : ℝ => if s ≤ σ then (1 : ℝ) else 0) =
      (Icc t σ).indicator (fun _ : ℝ => 1) := by
    funext s
    by_cases hts : t ≤ s
    · by_cases hsσ : s ≤ σ
      · simp [Set.indicator, hts, hsσ, hsσ.trans hσ1]
      · by_cases hs1 : s ≤ 1 <;> simp [Set.indicator, hts, hsσ, hs1]
    · simp [Set.indicator, hts]
  rw [← integral_indicator measurableSet_Icc, he, integral_indicator measurableSet_Icc,
    integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr htσ), smul_eq_mul, mul_one]

omit [MeasurableSpace Seed] in
lemma prefixSurvivalWeight_mul_integral (π : Policy Seed n) (W : Seed × History n → ℝ)
    (i : Fin n) (t : ℝ) (ω : World n Seed) :
    prefixSurvivalWeight π W i t ω *
      (∫ s in Icc t (1 : ℝ), (if s ≤ π.pendingTime ω.2.2 ω.1 ω.2.1 i then (1 : ℝ) else 0)) =
        prefixSurvivalWeight π W i t ω * (π.pendingTime ω.2.2 ω.1 ω.2.1 i - t) := by
  by_cases hs : t ≤ π.pendingTime ω.2.2 ω.1 ω.2.1 i
  · rw [survival_duration_integral hs (π.stoppingTime_le_one _ _ _ _)]
  · simp only [prefixSurvivalWeight, if_neg hs, mul_zero, zero_mul]

/-- The manuscript survival-integral form of `eq:ps-survival-allocation`.
The integrand uses the analytical pending execution, with reward-independent
terminal convention at time one. -/
lemma Instance.survival_allocation_integral (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A)
    {w c t K : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (ht0 : 0 < t) (ht1 : t < 1)
    (W : Seed × History n → ℝ) (hW : Measurable W) (hWbounds : ∀ z, 0 ≤ W z ∧ W z ≤ K) :
    let π := (P.valuePolicy hP hw.le hc).rule.withAuxiliarySeed (Seed := Seed)
    let ψ := (P.restrictTo A).valuePolicy (P.restrictTo_integrable_maximum A hP)
      hw.le (mul_nonneg hc (sub_nonneg.mpr ht1.le))
    let G := prefixSurvivalWeight π W i t
    (1 - t) * ψ.expectedDuration (P.restrictTo A) *
      (∫ ω in {ω : World n Seed | otherUnseen ω.2.1 i t = A}, G ω ∂P.worldLaw ν) ≤
      ∫ ω in {ω : World n Seed | otherUnseen ω.2.1 i t = A}, G ω *
        (∫ s in Icc t (1 : ℝ), (if s ≤ π.pendingTime ω.2.2 ω.1 ω.2.1 i then (1 : ℝ) else 0)) ∂P.worldLaw ν := by
  have h := P.survival_allocation hP ν A i hAi hw hc ht0 ht1 W hW hWbounds
  dsimp only at h ⊢
  calc
    _ ≤ _ := h
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun ω => (prefixSurvivalWeight_mul_integral _ W i t ω).symm)

omit [MeasurableSpace Seed] in
lemma observedPrefix_erase_candidate (i : Fin n) (t : ℝ) (ω : World n Seed) :
    observedPrefix i t (Instance.eraseWorld i ω) = observedPrefix i t ω := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [observedPrefix, history]
  · simp [observedPrefix, history, Instance.eraseWorld, eraseCoordinate, hji]

omit [MeasurableSpace Seed] in
lemma prefixSurvivalWeight_erase_candidate (π : Policy Seed n) (W : Seed × History n → ℝ)
    (i : Fin n) (t : ℝ) (ω : World n Seed) :
    prefixSurvivalWeight π W i t (Instance.eraseWorld i ω) = prefixSurvivalWeight π W i t ω := by
  unfold prefixSurvivalWeight
  rw [observedPrefix_erase_candidate]
  change W (ω.2.2, observedPrefix i t ω) *
    (if t ≤ π.pendingTime ω.2.2 (Function.update ω.1 i 0) (Function.update ω.2.1 i 0) i then 1 else 0) = _
  rw [π.pendingTime_update]

lemma measurable_world_otherUnseen (i : Fin n) (t : ℝ) :
    Measurable (fun ω : World n Seed => otherUnseen ω.2.1 i t) := by
  rw [measurable_finset_iff]
  intro j
  apply measurableSet_setOf.mp
  by_cases hji : j = i
  · subst j
    simp only [otherUnseen, Finset.mem_filter, Finset.mem_erase, ne_eq, not_true_eq_false,
      Finset.mem_univ, and_true, false_and, setOf_false]
    exact MeasurableSet.empty
  · simp only [otherUnseen, Finset.mem_filter, Finset.mem_erase, hji, not_false_eq_true,
      Finset.mem_univ, ne_eq, and_self, true_and]
    exact measurableSet_le measurable_const ((measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))

/-- Prefix survival jointly with the unseen state is independent of the pending
candidate's complete value/clock pair. Neither latent coordinate is supplied to
any prefix multiplier or policy. -/
lemma Instance.prefixSurvival_state_candidate_independent (P : Instance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Policy Seed n) (hπ : π.IsMeasurable)
    (W : Seed × History n → ℝ) (hW : Measurable W) (i : Fin n) (t : ℝ) :
    IndepFun (fun ω : World n Seed => (prefixSurvivalWeight π W i t ω, otherUnseen ω.2.1 i t))
      (fun ω => (ω.1 i, ω.2.1 i)) (P.worldLaw ν) := by
  apply P.erasedFunctional_candidate_independent ν i _
    ((measurable_prefixSurvivalWeight π hπ W hW i t).prodMk (measurable_world_otherUnseen i t))
  intro ω
  apply Prod.ext
  · exact prefixSurvivalWeight_erase_candidate π W i t ω
  · ext j
    by_cases hji : j = i
    · subst j
      simp [otherUnseen]
    · simp [otherUnseen, Instance.eraseWorld, eraseCoordinate, hji]

omit [MeasurableSpace Seed] in
lemma prefixSurvivalWeight_bounds (π : Policy Seed n) (W : Seed × History n → ℝ)
    {K : ℝ} (hW : ∀ z, 0 ≤ W z ∧ W z ≤ K) (i : Fin n) (t : ℝ) (ω : World n Seed) :
    0 ≤ prefixSurvivalWeight π W i t ω ∧ prefixSurvivalWeight π W i t ω ≤ K := by
  have hK : 0 ≤ K := (hW (ω.2.2, observedPrefix i t ω)).1.trans (hW (ω.2.2, observedPrefix i t ω)).2
  unfold prefixSurvivalWeight
  split_ifs
  · simpa only [mul_one] using hW (ω.2.2, observedPrefix i t ω)
  · simpa only [mul_zero] using And.intro (le_refl (0 : ℝ)) hK

lemma Instance.integrable_prefixSurvivalWeight (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy Seed n) (hπ : π.IsMeasurable) (W : Seed × History n → ℝ) (hW : Measurable W)
    {K : ℝ} (hWbounds : ∀ z, 0 ≤ W z ∧ W z ≤ K) (i : Fin n) (t : ℝ) :
    Integrable (prefixSurvivalWeight π W i t) (P.worldLaw ν) := by
  apply Integrable.of_bound (measurable_prefixSurvivalWeight π hπ W hW i t).aestronglyMeasurable K
  exact Filter.Eventually.of_forall fun ω => by
    have h := prefixSurvivalWeight_bounds π W hWbounds i t ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

lemma Instance.integrable_prefixSurvivalDuration (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy Seed n) (hπ : π.IsMeasurable) (W : Seed × History n → ℝ) (hW : Measurable W)
    {K : ℝ} (hWbounds : ∀ z, 0 ≤ W z ∧ W z ≤ K) (i : Fin n) (t : ℝ) :
    Integrable (fun ω => prefixSurvivalWeight π W i t ω * (π.pendingTime ω.2.2 ω.1 ω.2.1 i - t))
      (P.worldLaw ν) := by
  apply ((P.integrable_pendingTime ν π hπ i).sub (integrable_const t)).bdd_mul
    (measurable_prefixSurvivalWeight π hπ W hW i t).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    have h := prefixSurvivalWeight_bounds π W hWbounds i t ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

lemma Instance.integrable_prefixSurvivalIntegral (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy Seed n) (hπ : π.IsMeasurable) (W : Seed × History n → ℝ) (hW : Measurable W)
    {K : ℝ} (hWbounds : ∀ z, 0 ≤ W z ∧ W z ≤ K) (i : Fin n) (t : ℝ) :
    Integrable (fun ω => prefixSurvivalWeight π W i t ω *
      (∫ s in Icc t (1 : ℝ), (if s ≤ π.pendingTime ω.2.2 ω.1 ω.2.1 i then (1 : ℝ) else 0)))
        (P.worldLaw ν) := by
  exact (P.integrable_prefixSurvivalDuration ν π hπ W hW hWbounds i t).congr
    (Filter.Eventually.of_forall fun ω => (prefixSurvivalWeight_mul_integral π W i t ω).symm)

end ProphetSecretary.Model
