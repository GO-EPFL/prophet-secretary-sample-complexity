import ProphetSecretary.Probability.MinimumUniform
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The maximum of finitely many independent uniforms

The maximum of `m` independent uniforms has density `m * s^(m-1)` on the
unit interval. The sampler in `lem:planner-sampler` uses this law for its
remaining-time fraction.
-/

open MeasureTheory Set Filter
open scoped Classical ENNReal

namespace ProphetSecretary.Probability

noncomputable def uniformMaximum (m : ℕ) (hm : 1 ≤ m) (a : Fin m → ℝ) : ℝ :=
  Finset.univ.sup' (uniformMinimum_indices_nonempty hm) a

lemma measurable_uniformMaximum (m : ℕ) (hm : 1 ≤ m) :
    Measurable (uniformMaximum m hm) := by
  have h : Measurable (Finset.univ.sup' (uniformMinimum_indices_nonempty hm)
      (fun i (a : Fin m → ℝ) => a i)) :=
    Finset.sup'_induction (uniformMinimum_indices_nonempty hm) _
      (fun _f hf _g hg => hf.sup hg) (fun i _ => measurable_pi_apply i)
  convert h using 1
  funext a
  simp only [uniformMaximum, Finset.sup'_apply]

lemma uniformMaximum_mem_unit (m : ℕ) (hm : 1 ≤ m) :
    ∀ᵐ a ∂Model.Instance.clocksLaw m, uniformMaximum m hm a ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [Model.Instance.clocks_mem_unitInterval (n := m)] with a ha
  constructor
  · exact (ha ⟨0, by omega⟩).1.trans
      (Finset.le_sup' a (Finset.mem_univ (⟨0, by omega⟩ : Fin m)))
  · exact Finset.sup'_le (uniformMinimum_indices_nonempty hm) a (fun i _ => (ha i).2)

lemma uniformMaximum_lowerCDF (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    (Model.Instance.clocksLaw m).real {a | uniformMaximum m hm a ≤ t} =
      (max (min t 1) 0) ^ m := by
  have hSet : {a : Fin m → ℝ | uniformMaximum m hm a ≤ t} =
      Set.univ.pi (fun _ : Fin m => Iic t) := by
    ext a
    simp only [Set.mem_setOf_eq, uniformMaximum, Finset.sup'_le_iff, Finset.mem_univ,
      forall_true_left, Set.mem_pi, Set.mem_univ, Set.mem_Iic]
  change ((Model.Instance.clocksLaw m) {a | uniformMaximum m hm a ≤ t}).toReal = _
  rw [hSet, Model.Instance.clocksLaw, Measure.pi_pi, ENNReal.toReal_prod]
  change (∏ _i : Fin m, Model.Instance.uniformClock.real (Iic t)) = _
  simp only [uniformClock_lowerCDF, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma integral_uniformMaximumDensity (m : ℕ) (hm : 1 ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in Icc (0 : ℝ) t, (m : ℝ) * s ^ (m - 1)) = t ^ m := by
  have hm0 : m ≠ 0 := by omega
  have hstep : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hcast : ((m - 1 : ℕ) : ℝ) + 1 = m := by exact_mod_cast hstep
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_const_mul, integral_pow, hstep, hcast,
    zero_pow hm0, sub_zero]
  field_simp

/-- The explicit measure with the maximum-uniform density. -/
noncomputable def uniformMaximumDensityLaw (m : ℕ) : Measure ℝ :=
  Model.Instance.uniformClock.withDensity (fun s => ENNReal.ofReal ((m : ℝ) * s ^ (m - 1)))

lemma uniformMaximumDensityLaw_Iic (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    uniformMaximumDensityLaw m (Iic t) = ENNReal.ofReal ((max (min t 1) 0) ^ m) := by
  have hSet : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 (min t 1) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]
    tauto
  rw [uniformMaximumDensityLaw, withDensity_apply _ measurableSet_Iic,
    Model.Instance.uniformClock, Measure.restrict_restrict measurableSet_Iic, hSet]
  by_cases ht : t < 0
  · have hneg : min t 1 < 0 := (min_le_left _ _).trans_lt ht
    rw [Icc_eq_empty_of_lt hneg, Measure.restrict_empty, lintegral_zero_measure,
      max_eq_right hneg.le, zero_pow (by omega : m ≠ 0), ENNReal.ofReal_zero]
  · have hmin : 0 ≤ min t 1 := le_min (le_of_not_gt ht) zero_le_one
    have hc : Continuous (fun s : ℝ => (m : ℝ) * s ^ (m - 1)) := by fun_prop
    rw [← ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc]
    · rw [integral_uniformMaximumDensity m hm hmin, max_eq_left hmin]
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs.1 _)

/-- The maximum of the actual independent uniform draws has the stated density. -/
lemma map_uniformMaximum_eq_densityLaw (m : ℕ) (hm : 1 ≤ m) :
    (Model.Instance.clocksLaw m).map (uniformMaximum m hm) = uniformMaximumDensityLaw m := by
  have hMeas := measurable_uniformMaximum m hm
  haveI : IsProbabilityMeasure ((Model.Instance.clocksLaw m).map (uniformMaximum m hm)) :=
    Measure.isProbabilityMeasure_map hMeas.aemeasurable
  apply Measure.ext_of_Iic
  intro t
  rw [uniformMaximumDensityLaw_Iic m hm]
  have hCDF := uniformMaximum_lowerCDF m hm t
  rw [← hCDF, Measure.map_apply hMeas measurableSet_Iic]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

lemma lintegral_uniformMaximum (m : ℕ) (hm : 1 ≤ m) (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ a, f (uniformMaximum m hm a) ∂Model.Instance.clocksLaw m) =
      ∫⁻ s, ENNReal.ofReal ((m : ℝ) * s ^ (m - 1)) * f s
        ∂Model.Instance.uniformClock := by
  rw [← lintegral_map hf (measurable_uniformMaximum m hm), map_uniformMaximum_eq_densityLaw,
    uniformMaximumDensityLaw]
  exact lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf

end ProphetSecretary.Probability
