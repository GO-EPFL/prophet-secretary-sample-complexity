import ProphetSecretary.Model.BellmanValue

/-!
# Bochner first-arrival decomposition

The finite first-arrival regions partition the uniform clock cube outside null ties.
Their previously proved child sampling maps transfer integrable real functions, retaining
the original identity labels and the independent normalized future clocks.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model.Instance

variable {n : ℕ}

lemma firstRegion_partition_real (f : (Fin (n + 1) → ℝ) → ℝ)
    (u : Fin (n + 1) → ℝ) (hu : Function.Injective u) :
    (∑ i, (firstRegion i).indicator f u) = f u := by
  obtain ⟨i, _hi, hmin⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
  have himin : u ∈ firstRegion i := fun j => hmin j (Finset.mem_univ j)
  calc
    _ = (firstRegion i).indicator f u := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        apply Set.indicator_of_notMem
        intro hjmin
        exact hji (hu (le_antisymm (hjmin i) (himin j)))
      · intro hn
        exact False.elim (hn (Finset.mem_univ i))
    _ = f u := Set.indicator_of_mem himin f

/-- Actual real integral decomposition, including the derived residual-clock law. -/
theorem integral_firstArrival_child {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : Measurable f) (hI : Integrable f (clocksLaw (n + 1))) :
    (∫ u, f u ∂clocksLaw (n + 1)) =
      ∑ i : Fin (n + 1), ∫ t, (∫ v, f (firstChildClocks i (t, v))
        ∂clocksLaw (remainingSet i).card) ∂firstChildTimeLaw i := by
  calc
    _ = ∫ u, ∑ i : Fin (n + 1), (firstRegion i).indicator f u ∂clocksLaw (n + 1) := by
      apply integral_congr_ae
      filter_upwards [clocks_pairwise_distinct (n := n + 1)] with u hu
      exact (firstRegion_partition_real f u hu).symm
    _ = ∑ i : Fin (n + 1), ∫ u, (firstRegion i).indicator f u ∂clocksLaw (n + 1) :=
      integral_finsetSum _ (fun i _ => hI.indicator (measurableSet_firstRegion i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_indicator (measurableSet_firstRegion i)]
      have hp := firstChildClocks_measurePreserving i
      have hmap := integral_map (μ := (firstChildTimeLaw i).prod (clocksLaw (remainingSet i).card))
        hp.measurable.aemeasurable hf.aestronglyMeasurable
      rw [hp.map_eq] at hmap
      rw [hmap]
      exact integral_prod _ (hp.integrable_comp_of_integrable hI.integrableOn)

/-- Every normalized future clock is strictly positive almost surely. -/
lemma clocks_positive {m : ℕ} : ∀ᵐ u ∂clocksLaw m, ∀ i, 0 < u i := by
  rw [ae_all_iff]
  intro i
  have hn := (measurePreserving_eval (fun _ : Fin m => uniformClock) i).quasiMeasurePreserving.ae
    (uniformClock.ae_ne 0)
  filter_upwards [clocks_mem_unitInterval (n := m), hn] with u hu hne
  exact lt_of_le_of_ne (hu i).1 hne.symm

end ProphetSecretary.Model.Instance
