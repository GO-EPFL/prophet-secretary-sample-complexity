import ProphetSecretary.Probability.UniformMaximum

/-!
# A maximum drawn from a fixed uniform reservoir

Taking the maximum over a nonempty subset of an independent uniform vector
has the same law as drawing only that many uniforms. The ambient seed law
therefore need not change when the active subset changes.
-/

open MeasureTheory Set
open scoped Classical ENNReal BigOperators

namespace ProphetSecretary.Probability

noncomputable def uniformSubsetMaximum {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty)
    (u : Fin n → ℝ) : ℝ := D.sup' hD u

lemma measurable_uniformSubsetMaximum {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty) :
    Measurable (uniformSubsetMaximum D hD) := by
  have h : Measurable (D.sup' hD (fun i (u : Fin n → ℝ) => u i)) :=
    Finset.sup'_induction hD _ (fun _f hf _g hg => hf.sup hg)
      (fun i _ => measurable_pi_apply i)
  convert h using 1
  funext u
  simp only [uniformSubsetMaximum, Finset.sup'_apply]

lemma uniformSubsetMaximum_lowerCDF {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty) (t : ℝ) :
    (Model.Instance.clocksLaw n).real {u | uniformSubsetMaximum D hD u ≤ t} =
      (max (min t 1) 0) ^ D.card := by
  have hSet : {u : Fin n → ℝ | uniformSubsetMaximum D hD u ≤ t} =
      Set.univ.pi (fun i : Fin n => if i ∈ D then Iic t else Set.univ) := by
    ext u
    simp only [Set.mem_setOf_eq, uniformSubsetMaximum, Finset.sup'_le_iff, Set.mem_pi,
      Set.mem_univ, forall_true_left]
    constructor
    · intro h i
      by_cases hi : i ∈ D
      · simpa only [if_pos hi, Set.mem_Iic] using h i hi
      · simp only [if_neg hi, Set.mem_univ]
    · intro h i hi
      simpa only [if_pos hi, Set.mem_Iic] using h i
  change ((Model.Instance.clocksLaw n) {u | uniformSubsetMaximum D hD u ≤ t}).toReal = _
  rw [hSet, Model.Instance.clocksLaw, Measure.pi_pi, ENNReal.toReal_prod]
  have hFactor (i : Fin n) :
      (Model.Instance.uniformClock (if i ∈ D then Iic t else Set.univ)).toReal =
        if i ∈ D then max (min t 1) 0 else 1 := by
    by_cases hi : i ∈ D
    · rw [if_pos hi, if_pos hi]
      exact uniformClock_lowerCDF t
    · simp [hi]
  simp_rw [hFactor]
  rw [Finset.prod_ite_mem_eq, Finset.prod_const]

lemma map_uniformSubsetMaximum_eq_densityLaw {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty) :
    (Model.Instance.clocksLaw n).map (uniformSubsetMaximum D hD) =
      uniformMaximumDensityLaw D.card := by
  have hMeas := measurable_uniformSubsetMaximum D hD
  haveI : IsProbabilityMeasure ((Model.Instance.clocksLaw n).map (uniformSubsetMaximum D hD)) :=
    Measure.isProbabilityMeasure_map hMeas.aemeasurable
  apply Measure.ext_of_Iic
  intro t
  rw [uniformMaximumDensityLaw_Iic D.card (Nat.succ_le_of_lt (Finset.card_pos.mpr hD))]
  have hCDF := uniformSubsetMaximum_lowerCDF D hD t
  rw [← hCDF, Measure.map_apply hMeas measurableSet_Iic]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

lemma map_uniformSubsetMaximum_eq_uniformMaximum {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty) :
    (Model.Instance.clocksLaw n).map (uniformSubsetMaximum D hD) =
      (Model.Instance.clocksLaw D.card).map
        (uniformMaximum D.card (Nat.succ_le_of_lt (Finset.card_pos.mpr hD))) := by
  rw [map_uniformSubsetMaximum_eq_densityLaw, map_uniformMaximum_eq_densityLaw]

end ProphetSecretary.Probability
