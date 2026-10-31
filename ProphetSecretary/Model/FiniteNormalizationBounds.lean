import ProphetSecretary.Model.FiniteBaseNormalization
import Mathlib.Topology.Order.Basic

/-!
# Uniform cap, tail-profile and weight bounds after normalization

When the fixed base means lie in [1/2,3/2], the new cap is at most twice the
old cap and the new tail count at b is bounded by the old count at b/2.
One positive weight interval works for the whole family. Convergence of the
base means to one gives these conditions after a finite prefix, without any
bound on total first moments.
-/

open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Model
variable {n : ℕ}

lemma fixedBaseNormalization_inverse_bound {M : ℝ} (hM : 1/2≤M) : 0<M ∧ M⁻¹≤2 := by
  have hp : 0<M := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/2) hM
  refine ⟨hp,?_⟩
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hp).mpr (by linarith only [hM])

lemma Instance.fixedBaseNormalization_cap (P : Instance n) {M H : ℝ} (hM : 1/2≤M) (hH : 0≤H)
    (hCap : ∀ i, ∀ᵐ x ∂P.law i, x≤H) :
    ∀ i, ∀ᵐ y ∂(P.scale M⁻¹ (inv_nonneg.mpr (fixedBaseNormalization_inverse_bound hM).1.le)).law i, y≤2*H := by
  intro i
  apply (ae_map_iff (measurable_valueScale M⁻¹).aemeasurable measurableSet_Iic).mpr
  filter_upwards [hCap i] with x hx
  exact (mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (fixedBaseNormalization_inverse_bound hM).1.le)).trans
    (mul_le_mul_of_nonneg_right (fixedBaseNormalization_inverse_bound hM).2 hH)

lemma Instance.fixedBaseNormalization_tailCount (P : Instance n) {M : ℝ} (hM : 0<M) (b : ℝ) :
    (P.scale M⁻¹ (inv_nonneg.mpr hM.le)).tailCount b=P.tailCount (M*b) := by
  unfold Instance.tailCount
  apply Finset.sum_congr rfl
  intro i _
  change (((P.law i).map (M⁻¹*·)) (Ioi b)).toReal=(P.law i (Ioi (M*b))).toReal
  rw [Measure.map_apply (measurable_valueScale M⁻¹) measurableSet_Ioi]
  have hPre : (M⁻¹*·) ⁻¹' Ioi b=Ioi (M*b) := by
    ext x
    simp only [Set.mem_preimage,Set.mem_Ioi]
    rw [←div_eq_inv_mul,lt_div_iff₀ hM,mul_comm b M]
  rw [hPre]

lemma Instance.fixedBaseNormalization_tailCount_le (P : Instance n) {M : ℝ} (hM : 1/2≤M)
    {b : ℝ} (hb : 0≤b) :
    (P.scale M⁻¹ (inv_nonneg.mpr (fixedBaseNormalization_inverse_bound hM).1.le)).tailCount b≤P.tailCount (b/2) := by
  rw [P.fixedBaseNormalization_tailCount (fixedBaseNormalization_inverse_bound hM).1]
  apply P.tailCount_antitone
  have h := mul_le_mul_of_nonneg_right hM hb
  linarith only [h]

lemma fixedBaseNormalization_weight_interval {M w c : ℝ}
    (hM : M∈Icc (1/2 : ℝ) (3/2)) (hw : 0<w) (hc : 0<c) (hSum : w+c=1) :
    0<min w c/4 ∧ min w c/4<1/2 ∧
      finiteNormalizationRewardWeight M w c∈Icc (min w c/4) (1-min w c/4) := by
  have hMp := (fixedBaseNormalization_inverse_bound hM.1).1
  have hD : 0<w*M+c := finiteNormalizationDenominator_positive hMp hw hc.le
  have hProd := mul_le_mul_of_nonneg_left hM.2 hw.le
  have hDTwo : w*M+c≤2 := by nlinarith only [hProd,hSum,hw,hc]
  have hDFourM : w*M+c≤4*M := by linarith only [hDTwo,hM.1]
  have hWR : w/4≤finiteNormalizationRewardWeight M w c := by
    unfold finiteNormalizationRewardWeight
    apply (le_div_iff₀ hD).mpr
    have h := mul_le_mul_of_nonneg_left hDFourM hw.le
    nlinarith only [h]
  have hCR : c/4≤finiteNormalizationDurationWeight M w c := by
    unfold finiteNormalizationDurationWeight
    apply (le_div_iff₀ hD).mpr
    have h := mul_le_mul_of_nonneg_left hDTwo hc.le
    nlinarith only [h,hc]
  have hWeights := (finiteNormalizationWeights hMp hw hc.le).2.2
  have hMinW : min w c/4≤w/4 := div_le_div_of_nonneg_right (min_le_left w c) (by norm_num)
  have hMinC : min w c/4≤c/4 := div_le_div_of_nonneg_right (min_le_right w c) (by norm_num)
  refine ⟨div_pos (lt_min hw hc) (by norm_num),?_,hMinW.trans hWR,?_⟩
  · nlinarith only [min_le_left w c,min_le_right w c,hSum]
  · linarith only [hWeights,hMinC,hCR]

lemma exists_fixedBaseNormalization_tail (M : ℕ → ℝ) (hM : Tendsto M atTop (𝓝 (1 : ℝ))) :
    ∃ m0 : ℕ, ∀ m≥m0, M m∈Icc (1/2 : ℝ) (3/2) := by
  have h := hM.eventually (Ioo_mem_nhds (by norm_num : (1/2 : ℝ)<1) (by norm_num : (1 : ℝ)<3/2))
  exact Filter.eventually_atTop.mp (h.mono (fun _ hx => ⟨hx.1.le,hx.2.le⟩))

lemma fixedBaseNormalization_weights_tendsto (M : ℕ → ℝ) (hM : Tendsto M atTop (𝓝 (1 : ℝ)))
    {w c : ℝ} (hSum : w+c=1) :
    Tendsto (fun m => finiteNormalizationRewardWeight (M m) w c) atTop (𝓝 w) ∧
      Tendsto (fun m => finiteNormalizationDurationWeight (M m) w c) atTop (𝓝 c) := by
  have hD := (hM.const_mul w).add_const c
  have hD0 : w*(1 : ℝ)+c≠0 := by rw [mul_one,hSum];norm_num
  constructor
  · have h := (hM.const_mul w).div hD hD0
    change Tendsto (fun m => finiteNormalizationRewardWeight (M m) w c) atTop (𝓝 (w*1/(w*1+c))) at h
    simpa only [mul_one,hSum,div_one] using h
  · have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).div hD hD0
    change Tendsto (fun m => finiteNormalizationDurationWeight (M m) w c) atTop (𝓝 (c/(w*1+c))) at h
    simpa only [mul_one,hSum,div_one] using h

end ProphetSecretary.Model
