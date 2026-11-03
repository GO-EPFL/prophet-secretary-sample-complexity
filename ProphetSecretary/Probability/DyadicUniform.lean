import ProphetSecretary.Probability.OrderCDFUniform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Coupling uniform draws to finite grids

The rounding map is an analytical coupling from a continuous uniform draw.
The finite implementation uses a uniformly drawn grid index and the rational
division `gridPoint`; it does not compute a floor of an observed real number.
The endpoint one is sent to the last grid point, changing only a null input.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Probability

def gridPoint {K : Type*} [Field K] (N : ℕ) (j : Fin N) : K := (j.val : K) / (N : K)

lemma gridPoint_ratCast (N : ℕ) (j : Fin N) :
    ((gridPoint N j : ℚ) : ℝ) = (gridPoint N j : ℝ) := by simp [gridPoint]

noncomputable def uniformGridIndex (N : ℕ) (hN : 0 < N) (u : ℝ) : Fin N :=
  ⟨min (N - 1) ⌊(N : ℝ) * u⌋₊, lt_of_le_of_lt (min_le_left _ _) (by omega)⟩

noncomputable def uniformGridRound (N : ℕ) (hN : 0 < N) (u : ℝ) : ℝ :=
  gridPoint N (uniformGridIndex N hN u)

lemma measurable_uniformGridIndex (N : ℕ) (hN : 0 < N) : Measurable (uniformGridIndex N hN) := by
  have hfloor : Measurable (fun u : ℝ => min (N - 1) ⌊(N : ℝ) * u⌋₊) :=
    (measurable_of_countable (fun k : ℕ => min (N - 1) k)).comp
      ((measurable_const.mul measurable_id).nat_floor)
  apply measurable_to_countable'
  intro j
  have hset : (uniformGridIndex N hN) ⁻¹' {j} =
      (fun u : ℝ => min (N - 1) ⌊(N : ℝ) * u⌋₊) ⁻¹' {j.val} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff, uniformGridIndex]
  rw [hset]
  exact hfloor (measurableSet_singleton _)

lemma measurable_uniformGridRound (N : ℕ) (hN : 0 < N) : Measurable (uniformGridRound N hN) :=
  (measurable_of_countable (gridPoint (K := ℝ) N)).comp (measurable_uniformGridIndex N hN)

lemma uniformGridIndex_of_lt_one (N : ℕ) (hN : 0 < N) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (uniformGridIndex N hN u).val = ⌊(N : ℝ) * u⌋₊ := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hf : ⌊(N : ℝ) * u⌋₊ < N := (Nat.floor_lt (mul_nonneg hNr.le hu0)).2 (by nlinarith)
  exact min_eq_right (by omega)

lemma uniformGridRound_bounds (N : ℕ) (hN : 0 < N) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ uniformGridRound N hN u ∧ uniformGridRound N hN u ≤ u ∧
      u - uniformGridRound N hN u ≤ 1 / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  by_cases hu1 : u < 1
  · have hf := Nat.floor_le (mul_nonneg hNr.le hu.1)
    have hn := Nat.lt_floor_add_one ((N : ℝ) * u)
    have hdown : (⌊(N : ℝ) * u⌋₊ : ℝ) / N ≤ u := (div_le_iff₀ hNr).2 (by nlinarith)
    have herr : u < (⌊(N : ℝ) * u⌋₊ : ℝ) / N + 1 / N := by
      rw [← add_div]
      exact (lt_div_iff₀ hNr).2 (by nlinarith)
    simp only [uniformGridRound, gridPoint, uniformGridIndex_of_lt_one N hN hu.1 hu1]
    exact ⟨div_nonneg (Nat.cast_nonneg _) hNr.le, hdown, by linarith⟩
  · have hueq : u = 1 := le_antisymm hu.2 (le_of_not_gt hu1)
    subst u
    have hN1 : 1 ≤ N := hN
    have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    simp only [uniformGridRound, gridPoint, uniformGridIndex, mul_one, Nat.floor_natCast,
      min_eq_left (Nat.sub_le N 1), Nat.cast_sub hN1, Nat.cast_one]
    have he : 1 - ((N : ℝ) - 1) / N = 1 / (N : ℝ) := by field_simp; ring
    exact ⟨div_nonneg (by linarith) hNr.le, (div_le_one hNr).2 (by linarith), he.le⟩

lemma uniformGridIndex_cell (N : ℕ) (hN : 0 < N) (j : Fin N) :
    {u : ℝ | uniformGridIndex N hN u = j} =ᵐ[Model.Instance.uniformClock]
      Ico ((j.val : ℝ) / N) (((j.val : ℝ) + 1) / N) := by
  filter_upwards [uniformClock_mem_open_unit] with u hu
  apply propext
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hnonneg : 0 ≤ (N : ℝ) * u := mul_nonneg hNr.le hu.1.le
  change uniformGridIndex N hN u = j ↔ _
  rw [Fin.ext_iff, uniformGridIndex_of_lt_one N hN hu.1.le hu.2, Nat.floor_eq_iff hnonneg]
  change ((j.val : ℝ) ≤ (N : ℝ) * u ∧ (N : ℝ) * u < (j.val : ℝ) + 1) ↔
    ((j.val : ℝ) / N ≤ u ∧ u < ((j.val : ℝ) + 1) / N)
  constructor
  · intro h
    exact ⟨(div_le_iff₀ hNr).2 (by nlinarith [h.1]), (lt_div_iff₀ hNr).2 (by nlinarith [h.2])⟩
  · intro h
    have ha := (div_le_iff₀ hNr).1 h.1
    have hb := (lt_div_iff₀ hNr).1 h.2
    constructor <;> nlinarith

noncomputable def uniformGridIndexLaw (N : ℕ) (hN : 0 < N) : Measure (Fin N) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact (PMF.uniformOfFintype (Fin N)).toMeasure

instance uniformGridIndexLaw_probability (N : ℕ) (hN : 0 < N) :
    IsProbabilityMeasure (uniformGridIndexLaw N hN) := by
  unfold uniformGridIndexLaw
  infer_instance

lemma uniformGridIndexLaw_real_singleton (N : ℕ) (hN : 0 < N) (j : Fin N) :
    (uniformGridIndexLaw N hN).real {j} = 1 / (N : ℝ) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  simp [uniformGridIndexLaw, measureReal_def, one_div]

lemma uniformClock_grid_cell (N : ℕ) (hN : 0 < N) (j : Fin N) :
    Model.Instance.uniformClock.real (Ico ((j.val : ℝ) / N) (((j.val : ℝ) + 1) / N)) = 1 / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hj : (j.val : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
  have h0 : 0 ≤ (j.val : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hNr.le
  have h1 : ((j.val : ℝ) + 1) / N ≤ 1 := (div_le_one hNr).2 hj
  have hsub : Ico ((j.val : ℝ) / N) (((j.val : ℝ) + 1) / N) ⊆ Icc (0 : ℝ) 1 := by
    intro u hu
    exact ⟨h0.trans hu.1, hu.2.le.trans h1⟩
  rw [Model.Instance.uniformClock, measureReal_restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr hsub]
  change (volume (Ico ((j.val : ℝ) / N) (((j.val : ℝ) + 1) / N))).toReal = _
  rw [Real.volume_Ico, ENNReal.toReal_ofReal (by
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_right (by linarith) hNr.le)]
  field_simp
  ring

/-- The exact grid law is proved for the continuous-to-finite coupling map. -/
theorem map_uniformGridIndex (N : ℕ) (hN : 0 < N) :
    Model.Instance.uniformClock.map (uniformGridIndex N hN) = uniformGridIndexLaw N hN := by
  letI : IsProbabilityMeasure (Model.Instance.uniformClock.map (uniformGridIndex N hN)) :=
    Measure.isProbabilityMeasure_map (measurable_uniformGridIndex N hN).aemeasurable
  apply (MeasureTheory.ext_iff_measureReal_singleton).2
  intro j
  rw [uniformGridIndexLaw_real_singleton,
    map_measureReal_apply (measurable_uniformGridIndex N hN) (measurableSet_singleton j)]
  change Model.Instance.uniformClock.real {u | uniformGridIndex N hN u = j} = _
  rw [measureReal_congr (uniformGridIndex_cell N hN j), uniformClock_grid_cell N hN j]

end ProphetSecretary.Probability
