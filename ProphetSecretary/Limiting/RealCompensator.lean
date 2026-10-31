import ProphetSecretary.Limiting.PredictableCompensator

/-!
# Integrable real weighted compensator

Bounded nonnegative premiums have integrable reached sums. Their expectation
is the stopped intensity integral, with no factor depending on the number of
retained individuals or the analytical Poisson count.
-/

open MeasureTheory Set
open scoped BigOperators Classical ENNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def HybridRule.reachedPoissonPremium (π : HybridRule n Seed)
    (g : Point × Model.World n Seed → ℝ) (v : HybridWorld n Seed) : ℝ :=
  (π.reachedPoissonSum (fun q => ENNReal.ofReal (g q)) v).toReal

omit [MeasurableSpace Seed] in
lemma HybridRule.reachedPoissonSum_ofReal_lt_top (π : HybridRule n Seed)
    (g : Point × Model.World n Seed → ℝ) (v : HybridWorld n Seed) :
    π.reachedPoissonSum (fun q => ENNReal.ofReal (g q)) v < ∞ := by
  unfold HybridRule.reachedPoissonSum
  apply ENNReal.sum_lt_top.mpr
  intro j _
  split_ifs <;> simp

omit [MeasurableSpace Seed] in
lemma HybridRule.reachedPoissonPremium_eq_sum (π : HybridRule n Seed)
    (g : Point × Model.World n Seed → ℝ) (hgnn : ∀ q, 0 ≤ g q) (v : HybridWorld n Seed) :
    π.reachedPoissonPremium g v =
      ∑ j : Fin v.1.1, if π.ReachesPoisson v.2.2.2 v.2.1 v.2.2.1 v.1 j then g (v.1.2 j, v.2) else 0 := by
  unfold HybridRule.reachedPoissonPremium HybridRule.reachedPoissonSum
  rw [ENNReal.toReal_sum (fun j _ => by split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · exact ENNReal.toReal_ofReal (hgnn _)
  · rfl

omit [MeasurableSpace Seed] in
lemma HybridRule.stoppedPremium_ofReal_lt_top (π : HybridRule n Seed)
    (g : Point × Model.World n Seed → ℝ) (q : Point × HybridWorld n Seed) :
    π.stoppedPremium (fun q => ENNReal.ofReal (g q)) q < ∞ := by
  unfold HybridRule.stoppedPremium
  split_ifs <;> simp

lemma HybridRule.lintegral_stoppedPremium_le (π : HybridRule n Seed) (P : Model.Instance n)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : Point × Model.World n Seed → ℝ) {B : ℝ} (hbound : ∀ q, g q ≤ B) :
    (∫⁻ q, π.stoppedPremium (fun q => ENNReal.ofReal (g q)) q
      ∂(intensity μ).prod (hybridWorldLaw P μ ν)) ≤ ENNReal.ofReal B * (μ : Measure ℝ) univ := by
  calc
    _ ≤ ∫⁻ _q : Point × HybridWorld n Seed, ENNReal.ofReal B
        ∂(intensity μ).prod (hybridWorldLaw P μ ν) := by
      apply lintegral_mono
      intro q
      unfold HybridRule.stoppedPremium
      split_ifs
      · exact ENNReal.ofReal_le_ofReal (hbound _)
      · exact zero_le
    _ = _ := by
      rw [lintegral_const]
      rw [← univ_prod_univ, Measure.prod_prod, measure_univ (μ := hybridWorldLaw P μ ν), mul_one]
      change ENNReal.ofReal B * (Model.Instance.uniformClock.prod (μ : Measure ℝ)) univ = _
      rw [← univ_prod_univ, Measure.prod_prod, measure_univ (μ := Model.Instance.uniformClock), one_mul]

lemma HybridRule.integrable_reachedPoissonPremium (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : Point × Model.World n Seed → ℝ) (hg : Measurable g)
    {B : ℝ} (hbound : ∀ q, g q ≤ B) :
    Integrable (π.reachedPoissonPremium g) (hybridWorldLaw P μ ν) := by
  apply integrable_toReal_of_lintegral_ne_top (π.measurable_reachedPoissonSum hπ _ hg.ennreal_ofReal).aemeasurable
  rw [π.weighted_poisson_compensator hπ P μ ν _ hg.ennreal_ofReal]
  exact ne_of_lt ((π.lintegral_stoppedPremium_le P μ ν g hbound).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)))

lemma HybridRule.weighted_poisson_compensator_real (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : Point × Model.World n Seed → ℝ) (hg : Measurable g) (hgnn : ∀ q, 0 ≤ g q)
    :
    (∫ v, π.reachedPoissonPremium g v ∂hybridWorldLaw P μ ν) =
      ∫ q, if q.1.1 ≤ π.realizedDuration q.2 then g (q.1, q.2.2) else 0
        ∂(intensity μ).prod (hybridWorldLaw P μ ν) := by
  change (∫ v, (π.reachedPoissonSum (fun q => ENNReal.ofReal (g q)) v).toReal ∂_) = _
  rw [integral_toReal (π.measurable_reachedPoissonSum hπ _ hg.ennreal_ofReal).aemeasurable
      (Filter.Eventually.of_forall (π.reachedPoissonSum_ofReal_lt_top g)),
    π.weighted_poisson_compensator hπ P μ ν _ hg.ennreal_ofReal,
    ← integral_toReal (π.measurable_stoppedPremium hπ _ hg.ennreal_ofReal).aemeasurable
      (Filter.Eventually.of_forall (π.stoppedPremium_ofReal_lt_top g))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q => by
    change (if q.1.1 ≤ π.realizedDuration q.2 then ENNReal.ofReal (g (q.1, q.2.2)) else 0).toReal = _
    by_cases hq : q.1.1 ≤ π.realizedDuration q.2
    · simp only [hq, if_true, ENNReal.toReal_ofReal (hgnn _)]
    · simp only [hq, if_false, ENNReal.toReal_zero])

lemma HybridRule.integrable_stoppedPoissonPremium (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : Point × Model.World n Seed → ℝ) (hg : Measurable g) (hgnn : ∀ q, 0 ≤ g q)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ q, g q ≤ B) :
    Integrable (fun q : Point × HybridWorld n Seed =>
      if q.1.1 ≤ π.realizedDuration q.2 then g (q.1, q.2.2) else 0)
      ((intensity μ).prod (hybridWorldLaw P μ ν)) := by
  have hm : Measurable (fun q : Point × HybridWorld n Seed =>
      if q.1.1 ≤ π.realizedDuration q.2 then g (q.1, q.2.2) else 0) := Measurable.ite (measurableSet_le (measurable_fst.comp measurable_fst)
    ((π.measurable_realizedDuration hπ).comp measurable_snd))
    (hg.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))) measurable_const
  apply Integrable.of_bound hm.aestronglyMeasurable B
  exact Filter.Eventually.of_forall (fun q => by
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (hgnn _)]
      exact hbound _
    · simpa only [norm_zero] using hB)

lemma HybridRule.weighted_poisson_compensator_real_iterated (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : Point × Model.World n Seed → ℝ) (hg : Measurable g) (hgnn : ∀ q, 0 ≤ g q)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ q, g q ≤ B) :
    (∫ v, π.reachedPoissonPremium g v ∂hybridWorldLaw P μ ν) =
      ∫ v, ∫ t, if t ≤ π.realizedDuration v then
        ∫ x, g ((t, x), v.2) ∂(μ : Measure ℝ) else 0
        ∂Model.Instance.uniformClock ∂hybridWorldLaw P μ ν := by
  rw [π.weighted_poisson_compensator_real hπ P μ ν g hg hgnn,
    integral_prod_symm _ (π.integrable_stoppedPoissonPremium hπ P μ ν g hg hgnn hB hbound)]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun v => ?_)
  have hm : Measurable (fun p : Point => if p.1 ≤ π.realizedDuration v then g (p, v.2) else 0) :=
    Measurable.ite (measurableSet_le measurable_fst measurable_const)
      (hg.comp (measurable_id.prodMk measurable_const)) measurable_const
  have hi : Integrable (fun p : Point => if p.1 ≤ π.realizedDuration v then g (p, v.2) else 0) (intensity μ) := by
    apply Integrable.of_bound hm.aestronglyMeasurable B
    exact Filter.Eventually.of_forall (fun p => by
      split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (hgnn _)]
        exact hbound _
      · simpa only [norm_zero] using hB)
  dsimp only
  rw [intensity, integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    by_cases ht : t ≤ π.realizedDuration v
    · simp only [ht, if_true]
    · simp only [ht, if_false, integral_zero])

end ProphetSecretary.Limiting
