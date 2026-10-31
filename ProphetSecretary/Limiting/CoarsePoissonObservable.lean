import ProphetSecretary.Limiting.HybridFiniteScoredEvaluation
import ProphetSecretary.Limiting.CoarseOutcomeTests

/-!
# The high-point outcome observable on actual Poisson evaluation laws

The full point measure is analytical input to an outcome functional. The
executed hybrid callback still receives only strict past observations. On
positive cap-bounded Poisson laws the observable equals actual reward and
elapsed duration, including the zero-intensity boundary.
-/
open MeasureTheory Set
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Limiting
variable {n N : ℕ}

noncomputable def hybridOutcomeObservable (π : RandomizedHybridPolicy n)
    (Φ : (ℝ × ℝ) × Model.World n π.Seed → ℝ) (q : (Measure Point) × Model.World n π.Seed) : ℝ :=
  Φ ((π.rule.observableReward 0 (ProphetSecretary.Probability.finiteMeasureOrZero q.1,q.2),
    π.rule.observableDuration (ProphetSecretary.Probability.finiteMeasureOrZero q.1,q.2)),q.2)

lemma measurable_hybridOutcomeObservable (π : RandomizedHybridPolicy n)
    (Φ : (ℝ × ℝ) × Model.World n π.Seed → ℝ) (hΦ : Measurable Φ) : Measurable (hybridOutcomeObservable π Φ) := by
  have hObs : Measurable (fun q : (Measure Point) × Model.World n π.Seed =>
      (ProphetSecretary.Probability.finiteMeasureOrZero q.1,q.2)) :=
    (ProphetSecretary.Probability.measurable_finiteMeasureOrZero.comp measurable_fst).prodMk measurable_snd
  exact hΦ.comp ((((π.rule.measurable_observableReward π.measurable_rule 0).comp hObs).prodMk
    ((π.rule.measurable_observableDuration π.measurable_rule).comp hObs)).prodMk measurable_snd)

lemma thresholdMarkIntensity_sum_supported (Q : Model.Instance N) {d H : ℝ} (hd : 0≤d)
    (hCap : ∀ j, ∀ᵐ x ∂Q.law j, x≤H) :
    ∀ᵐ x ∂((∑ j, thresholdMarkIntensity (Q.law j) d : FiniteMeasure ℝ):Measure ℝ), x∈Ioc (0:ℝ) H := by
  rw [FiniteMeasure.toMeasure_sum,ae_finsetSum_measure_iff]
  intro j _
  change ∀ᵐ x ∂(Q.law j).restrict (Ioi d), x∈Ioc (0:ℝ) H
  filter_upwards [ae_restrict_mem measurableSet_Ioi,ae_restrict_of_ae (hCap j)] with x hx hH
  exact ⟨hd.trans_lt hx,hH⟩

lemma hybridOutcomeObservable_eq_ae (π : RandomizedHybridPolicy n) (P : Model.Instance n) (μ : FiniteMeasure ℝ)
    (H : ℝ≥0) (hP : ∀ i, ∀ᵐ x ∂P.law i, x≤(H:ℝ))
    (hμ : ∀ᵐ x ∂(μ:Measure ℝ), x∈Ioc (0:ℝ) H)
    (Φ : (ℝ × ℝ) × Model.World n π.Seed → ℝ) :
    ∀ᵐ v ∂hybridWorldLaw P μ π.seedLaw, hybridOutcomeObservable π Φ (countingMeasure v.1,v.2)=
      Φ ((π.rule.realizedReward 0 v,π.rule.realizedDuration v),v.2) := by
  filter_upwards [realized_values_bounds P μ π.seedLaw hP hμ,
    hybrid_combined_clocks_regular P μ π.seedLaw] with v hx ht
  have hu (k) : combinedClocks v.2.2.1 v.1.2 k∈Icc (0:ℝ) 1 := ⟨(ht.2 k).1.le,(ht.2 k).2.le⟩
  have hR := π.rule.hybridReward_eq_observable π.measurable_rule v hu (fun k => (hx k).1) ht.1 0
  have hT := π.rule.hybridDuration_eq_observable π.measurable_rule v hu
  exact congrArg Φ (Prod.ext (Prod.ext hR hT) rfl)

lemma hybrid_policy_outcome_ranges (π : RandomizedHybridPolicy n) (P : Model.Instance n) (μ : FiniteMeasure ℝ)
    (H : ℝ≥0) (hP : ∀ i, ∀ᵐ x ∂P.law i, x≤(H:ℝ))
    (hμ : ∀ᵐ x ∂(μ:Measure ℝ), x∈Ioc (0:ℝ) H) :
    ∀ᵐ v ∂hybridWorldLaw P μ π.seedLaw,
      π.rule.realizedReward 0 v∈Icc (0:ℝ) H ∧ π.rule.realizedDuration v∈Icc (0:ℝ) 1 := by
  filter_upwards [realized_values_bounds P μ π.seedLaw hP hμ,
    hybrid_combined_clocks_regular P μ π.seedLaw] with v hx ht
  have hR0 := π.rule.reward_nonnegative (by norm_num : (0:ℝ)≤0) v.2.2.2 v.2.1 v.2.2.1 v.1 (fun k => (hx k).1)
  have hRH := (π.rule.reward_le_maximum 0 v.2.2.2 v.2.1 v.2.2.1 v.1).trans
    (hybridMaximum_le H.property H.property (v.1,v.2.1) (fun k => (hx k).2))
  exact ⟨⟨hR0,hRH⟩,⟨(π.rule.asFinitePolicy v.1.1).stoppingTime_nonneg _ _ _ _ (fun k => (ht.2 k).1.le),
    (π.rule.asFinitePolicy v.1.1).stoppingTime_le_one _ _ _ _⟩⟩
end ProphetSecretary.Limiting
