import ProphetSecretary.Reach.FiniteReach
import ProphetSecretary.Reach.AlmostEverywhereQuadraticReach
import ProphetSecretary.Model.ClockReplacement

/-!
# Strict reach from an established pending-execution comparison

This common integration argument is conditional on a pathwise comparison on valid
complete executions. Markov deletion-monotone rules derive that comparison from their
history-based decisions in `MarkovAcceptance`; it is not assumed as their interface.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

/-- The selection-duration quadratic bound once pending domination has actually been
proved on nonnegative offer vectors and unit clock vectors. Off-support decisions remain
unconstrained. -/
theorem Policy.strict_reach_of_pending_domination
    (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n)
    (hdom : ∀ (r : Seed) (x u : Fin n → ℝ), (∀ j, 0 ≤ x j) →
      (∀ j, u j ∈ Icc (0 : ℝ) 1) →
      π.stoppingTime r Finset.univ x u ≤ π.pendingTime r x u i) :
    π.reachProbability P ν i - π.meanDuration P ν ≥ (π.selectionProbability P ν i) ^ 2 / 2 := by
  let μ := P.worldLaw ν
  let σ : World n Seed → ℝ := fun ω ↦ π.pendingTime ω.2.2 ω.1 ω.2.1 i
  let d : World n Seed → ℝ := fun ω ↦ π.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
  let E : Set (World n Seed) := {ω | π.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i}
  let a₀ : World n Seed → ℝ := fun ω ↦ if ω ∈ E then 1 else 0
  let a : World n Seed × ℝ → ℝ := a₀ ∘ Instance.replaceClock i
  let τ : World n Seed × ℝ → ℝ := d ∘ Instance.replaceClock i
  have hrep := P.replaceClock_measurePreserving ν i
  have hσm : Measurable σ := π.measurable_pendingWorldTime hπ i
  have hdm : Measurable d := π.measurable_worldTime hπ Finset.univ
  have hEm : MeasurableSet E := π.measurableSet_actualSelects hπ
    (measurable_snd.comp measurable_snd)
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))
    Finset.univ i
  have ha₀m : Measurable a₀ := Measurable.ite hEm measurable_const measurable_const
  have ham : Measurable a := ha₀m.comp hrep.measurable
  have hσ01 : ∀ᵐ ω ∂μ, σ ω ∈ Icc (0 : ℝ) 1 := P.pendingTime_mem_unitInterval ν π i
  have hσI : Integrable σ μ := P.integrable_pendingTime ν π hπ i
  have ha01 : ∀ z, a z ∈ Icc (0 : ℝ) 1 := by
    intro z
    dsimp [a, a₀]
    split_ifs <;> norm_num
  have haI : Integrable a (μ.prod Instance.uniformClock) :=
    ProphetSecretary.Reach.integrable_of_ae_unit _ ham.aestronglyMeasurable (Filter.Eventually.of_forall ha01)
  have hτI : Integrable τ (μ.prod Instance.uniformClock) :=
    hrep.integrable_comp_of_integrable (P.integrable_worldTime ν π hπ Finset.univ)
  have hclock : ∀ᵐ z : World n Seed × ℝ ∂μ.prod Instance.uniformClock,
      z.2 ∈ Icc (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := Instance.uniformClock)).ae
      (ae_restrict_mem measurableSet_Icc)
  have hσprod : ∀ᵐ z : World n Seed × ℝ ∂μ.prod Instance.uniformClock,
      σ z.1 ∈ Icc (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := Instance.uniformClock)).ae hσ01
  have hWI : Integrable (fun z : World n Seed × ℝ ↦ (σ z.1 - z.2) * a z)
      (μ.prod Instance.uniformClock) := by
    apply Integrable.of_bound ((hσm.comp measurable_fst).sub measurable_snd |>.mul ham).aestronglyMeasurable 1
    filter_upwards [hclock, hσprod] with z ht hs
    have hd : ‖σ z.1 - z.2‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    have hab : ‖a z‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (ha01 z).1]
      exact (ha01 z).2
    change ‖(σ z.1 - z.2) * a z‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul hd hab (norm_nonneg _) zero_le_one).trans (by norm_num)
  have hrepσ : ∀ z : World n Seed × ℝ,
      π.pendingTime (Instance.replaceClock i z).2.2 (Instance.replaceClock i z).1
        (Instance.replaceClock i z).2.1 i = σ z.1 :=
    fun z ↦ Instance.pendingTime_replaceClock π i z
  have hxnonneg : ∀ᵐ ω : World n Seed ∂μ, ∀ j, 0 ≤ ω.1 j := by
    exact (measurePreserving_fst (μ := P.valuesLaw) (ν := (Instance.clocksLaw n).prod ν)).quasiMeasurePreserving.ae P.ae_nonnegative
  have hstop : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, τ (ω, t) ≤ σ ω := by
    filter_upwards [hxnonneg, P.world_clocks_mem_unitInterval ν] with ω hx hu t ht
    have hc : ∀ j, (Instance.replaceClock i (ω, t)).2.1 j ∈ Icc (0 : ℝ) 1 := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [Instance.replaceClock, Function.update_self] using ht
      · simpa only [Instance.replaceClock, Function.update_of_ne hji] using hu j
    have h := hdom (Instance.replaceClock i (ω, t)).2.2
      (Instance.replaceClock i (ω, t)).1 (Instance.replaceClock i (ω, t)).2.1 hx hc
    rw [hrepσ (ω, t)] at h
    exact h
  have hselected : ∀ z : World n Seed × ℝ,
      Instance.replaceClock i z ∈ E → τ z = z.2 := by
    intro z hz
    have h := hz.1.2
    simpa only [τ, d, Function.comp_apply, Instance.replaceClock, Function.update_self] using h.symm
  have hsupport : ∀ᵐ ω ∂μ, ∀ t ∈ Ioo (σ ω) 1, a (ω, t) = 0 := by
    filter_upwards [hstop, hσ01] with ω hω hσ t ht
    dsimp [a, a₀]
    rw [if_neg]
    intro h
    have hs := hω t ⟨hσ.1.trans ht.1.le, ht.2.le⟩
    rw [hselected (ω, t) h] at hs
    exact (not_le.mpr ht.1) hs
  have hgap : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1,
      (σ ω - t) * a (ω, t) ≤ σ ω - τ (ω, t) := by
    filter_upwards [hstop] with ω hω t ht
    dsimp [a, a₀]
    split_ifs with h
    · rw [mul_one, hselected (ω, t) h]
    · rw [mul_zero]
      exact sub_nonneg.mpr (hω t ht)
  have hquad := ProphetSecretary.Reach.quadratic_gap_product_ae μ hσ01 hσI haI hτI hWI
    (Filter.Eventually.of_forall (fun ω t _ht ↦ ha01 (ω, t))) hsupport hgap
  have hcomp (f : World n Seed → ℝ) (hf : Measurable f) :
      (∫ z, f (Instance.replaceClock i z) ∂μ.prod Instance.uniformClock) = ∫ ω, f ω ∂μ := by
    have h := integral_map (μ := μ.prod Instance.uniformClock)
      hrep.measurable.aemeasurable hf.aestronglyMeasurable
    rw [hrep.map_eq] at h
    exact h.symm
  have hAeq : (∫ z, a z ∂μ.prod Instance.uniformClock) = π.selectionProbability P ν i := by
    change (∫ z, a₀ (Instance.replaceClock i z) ∂μ.prod Instance.uniformClock) = _
    rw [hcomp a₀ ha₀m]
    simpa only [a₀, Policy.selectionProbability, E, Set.indicator_apply,
      Set.mem_setOf_eq, Pi.one_apply] using (integral_indicator_one (μ := μ) hEm)
  have hTeq : (∫ z, τ z ∂μ.prod Instance.uniformClock) = π.meanDuration P ν := by
    exact hcomp d hdm
  change (∫ z, a z ∂μ.prod Instance.uniformClock) ^ 2 / 2 ≤
    (∫ ω, σ ω ∂μ) - ∫ z, τ z ∂μ.prod Instance.uniformClock at hquad
  rw [hAeq, hTeq] at hquad
  change π.selectionProbability P ν i ^ 2 / 2 ≤
    (∫ ω : World n Seed, π.pendingTime ω.2.2 ω.1 ω.2.1 i ∂P.worldLaw ν) -
      π.meanDuration P ν at hquad
  rw [← π.reachProbability_eq_mean_pending hπ P ν i] at hquad
  exact hquad


end ProphetSecretary.Model
