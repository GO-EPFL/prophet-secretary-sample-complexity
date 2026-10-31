import ProphetSecretary.Limiting.HybridCompensator

/-!
# Weighted compensator for a hybrid execution

A premium may depend on the candidate time and mark and on the retained
individual world. Removing an anonymous candidate preserves the retained data,
so the constructed Mecke identity gives its stopped integral.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def HybridRule.reachedPoissonSum (π : HybridRule n Seed)
    (g : Point × Model.World n Seed → ℝ≥0∞) (v : HybridWorld n Seed) : ℝ≥0∞ :=
  ∑ j : Fin v.1.1, if π.ReachesPoisson v.2.2.2 v.2.1 v.2.2.1 v.1 j then g (v.1.2 j, v.2) else 0

noncomputable def HybridRule.stoppedPremium (π : HybridRule n Seed)
    (g : Point × Model.World n Seed → ℝ≥0∞) (q : Point × HybridWorld n Seed) : ℝ≥0∞ :=
  if q.1.1 ≤ π.realizedDuration q.2 then g (q.1, q.2.2) else 0

lemma HybridRule.measurable_stoppedPremium (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (g : Point × Model.World n Seed → ℝ≥0∞) (hg : Measurable g) : Measurable (π.stoppedPremium g) := by
  apply Measurable.ite (measurableSet_le (measurable_fst.comp measurable_fst)
    ((π.measurable_realizedDuration hπ).comp measurable_snd))
  · exact hg.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  · exact measurable_const

lemma HybridRule.measurable_reachedPoissonSum (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (g : Point × Model.World n Seed → ℝ≥0∞) (hg : Measurable g) : Measurable (π.reachedPoissonSum g) := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × Model.World n Seed
  have hr : Measurable (fun v : Ω => v.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hx (i : Fin n) : Measurable (fun v : Ω => v.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hu (i : Fin n) : Measurable (fun v : Ω => v.2.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hv (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  change Measurable (fun v : Ω => ∑ j : Fin N, if
    (π.asFinitePolicy N).Reaches v.2.2.2 (combinedValues v.2.1 v.1) (combinedClocks v.2.2.1 v.1) (j.natAdd n)
      then g (v.1 j, v.2) else 0)
  apply Finset.measurable_fun_sum
  intro j _
  exact Measurable.ite ((π.asFinitePolicy N).measurableSet_reaches (π.asFinitePolicy_isMeasurable hπ N) hr
    (fun k => measurable_combinedValues_family _ hx _ hv k)
    (fun k => measurable_combinedClocks_family _ hu _ hv k) (j.natAdd n))
    (hg.comp ((hv j).prodMk measurable_snd)) measurable_const

lemma HybridRule.mecke_stoppedPremium_ae (π : HybridRule n Seed) (P : Model.Instance n)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : Point × Model.World n Seed → ℝ≥0∞) :
    meckeSum (π.stoppedPremium g) =ᵐ[hybridWorldLaw P μ ν] π.reachedPoissonSum g := by
  have hc := (Measure.quasiMeasurePreserving_fst (μ := configurationLaw μ) (ν := P.worldLaw ν)).ae
    (configuration_times_mem_Ioo μ)
  filter_upwards [hc] with v hv
  unfold meckeSum HybridRule.reachedPoissonSum
  apply Finset.sum_congr rfl
  intro j _
  have he := π.reachesPoisson_iff_le_deleted v.2.2.2 v.2.1 v.2.2.1 v.1 j (hv j).2.le
  change (if (v.1.2 j).1 ≤ π.stoppingTime v.2.2.2 v.2.1 v.2.2.1 (erasePoint v.1 j)
    then g (v.1.2 j, v.2) else 0) = _
  exact ite_congr (propext he.symm) (fun _ => rfl) (fun _ => rfl)

/-- The premium need not be independent of the stopping event. -/
lemma HybridRule.weighted_poisson_compensator (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : Point × Model.World n Seed → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ v, π.reachedPoissonSum g v ∂hybridWorldLaw P μ ν) =
      ∫⁻ q, π.stoppedPremium g q ∂(intensity μ).prod (hybridWorldLaw P μ ν) := by
  calc
    _ = ∫⁻ v, meckeSum (π.stoppedPremium g) v ∂hybridWorldLaw P μ ν :=
      (lintegral_congr_ae (π.mecke_stoppedPremium_ae P μ ν g)).symm
    _ = _ := mecke μ (P.worldLaw ν) _ (π.measurable_stoppedPremium hπ g hg)

lemma HybridRule.weighted_poisson_compensator_iterated (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (g : Point × Model.World n Seed → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ v, π.reachedPoissonSum g v ∂hybridWorldLaw P μ ν) =
      ∫⁻ v, ∫⁻ t, if t ≤ π.realizedDuration v then
        ∫⁻ x, g ((t, x), v.2) ∂(μ : Measure ℝ) else 0
        ∂Model.Instance.uniformClock ∂hybridWorldLaw P μ ν := by
  rw [π.weighted_poisson_compensator hπ P μ ν g hg,
    lintegral_prod_symm _ (π.measurable_stoppedPremium hπ g hg).aemeasurable]
  apply lintegral_congr
  intro v
  have hm : Measurable (fun p : Point => π.stoppedPremium g (p, v)) :=
    (π.measurable_stoppedPremium hπ g hg).comp (measurable_id.prodMk measurable_const)
  rw [intensity, lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro t
  by_cases ht : t ≤ π.realizedDuration v
  · simp only [HybridRule.stoppedPremium, ht, if_true]
  · simp only [HybridRule.stoppedPremium, ht, if_false, lintegral_zero]

end ProphetSecretary.Limiting
