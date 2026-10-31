import ProphetSecretary.Model.EmpiricalTimeRegionCover

/-!
# Integrating the actual empirical-loss region cover

Nonnegative candidate-time loss over the unit horizon is bounded by its near
and far integrals plus the early-band series. Countably many entrance points
are removed only as null time sets; no integrability assumption is hidden in
the decomposition, which is stated first for nonnegative Lebesgue integrals.
-/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem Instance.empirical_time_integral_cover_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {hi a z x : ℝ}
    (hhi : 0 ≤ hi) (ha : 0 < a) (u : Fin n → ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Icc (0 : ℝ) 1, f t) ≤
      (∫⁻ t in Ioc (P.trueCriticalEntrance hi a u) 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t}, f t) +
      (∫⁻ t in Ioc (P.trueCriticalEntrance hi a u) 1 ∩ {t | P.clockContinuation z u t < x / 2}, f t) +
      ∑' j : ℕ, ∫⁻ t in Ioc (P.trueCriticalEntrance hi (2 * ((2 : ℝ) ^ j * a)) u) 1 ∩
        {t | (2 : ℝ) ^ j * a ≤ P.clockContinuation hi u t}, f t := by
  let N := Ioc (P.trueCriticalEntrance hi a u) 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t}
  let F := Ioc (P.trueCriticalEntrance hi a u) 1 ∩ {t | P.clockContinuation z u t < x / 2}
  let E := fun j : ℕ => Ioc (P.trueCriticalEntrance hi (2 * ((2 : ℝ) ^ j * a)) u) 1 ∩
    {t | (2 : ℝ) ^ j * a ≤ P.clockContinuation hi u t}
  let U := (N ∪ F) ∪ ⋃ j : ℕ, E j
  have hcover : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), t ∈ U := by
    filter_upwards [P.empirical_time_region_cover_ae (z := z) (x := x) hP hhi ha u] with t ht
    rcases ht with ht | ht | ⟨j, ht⟩
    · exact Or.inl (Or.inl ht)
    · exact Or.inl (Or.inr ht)
    · exact Or.inr (mem_iUnion.mpr ⟨j, ht⟩)
  have hphysical (b t : ℝ) (ht : t ∈ Ioc (P.trueCriticalEntrance hi b u) 1) : t ∈ Icc (0 : ℝ) 1 :=
    ⟨(P.trueCriticalEntrance_mem hi b u).1.trans ht.1.le, ht.2⟩
  have hsub : U ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    rcases ht with (ht | ht) | ht
    · exact hphysical a t ht.1
    · exact hphysical a t ht.1
    · obtain ⟨j, hj⟩ := mem_iUnion.mp ht
      exact hphysical _ t hj.1
  have hglobal := (ae_restrict_iff' measurableSet_Icc).mp hcover
  have heq : Icc (0 : ℝ) 1 =ᵐ[volume] U := by
    filter_upwards [hglobal] with t ht
    exact propext ⟨ht, fun h => hsub h⟩
  rw [Measure.restrict_congr_set heq]
  have h1 := lintegral_union_le (μ := volume) f (N ∪ F) (⋃ j : ℕ, E j)
  have h2 := lintegral_union_le (μ := volume) f N F
  have h3 := lintegral_iUnion_le (μ := volume) E f
  exact h1.trans (add_le_add h2 h3)

end ProphetSecretary.Model
