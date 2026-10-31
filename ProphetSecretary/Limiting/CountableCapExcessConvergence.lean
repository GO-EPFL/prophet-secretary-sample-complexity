import ProphetSecretary.Limiting.CountableCapExcess
import ProphetSecretary.Limiting.HybridCapExcess
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Aggregate excess under moving positive caps and countable truncation

A fixed lower positive cap dominates every sufficiently late excess kernel.
Its summable individual expectations and integrable anonymous excess give
Tannery and dominated-convergence bounds. A cutoff below the cap discards
only zero excess. Thus retained dimension and cutoff may converge jointly,
with atoms allowed at the moving cap.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology Classical BigOperators
namespace ProphetSecretary.Limiting.CountableInstance

lemma individualCapExcess_antitone (B : CountableInstance) (i : ℕ) : Antitone (fun K : ℝ≥0 => B.individualCapExcess K i) := by
  intro K H hKH
  apply integral_mono (B.individualCapExcess_integrable H i) (B.individualCapExcess_integrable K i)
  intro x
  have hKHR : (K:ℝ)≤(H:ℝ) := by exact_mod_cast hKH
  exact max_le_max (sub_le_sub_left hKHR x) le_rfl

lemma individualCapExcess_tendsto (B : CountableInstance) {Ks : ℕ → ℝ≥0} {K : ℝ≥0}
    (hKLimit : Tendsto Ks atTop (𝓝 K)) (i : ℕ) :
    Tendsto (fun m => B.individualCapExcess (Ks m) i) atTop (𝓝 (B.individualCapExcess K i)) :=
  finiteMeasure_tailValue_tendsto (B.individuals i).toFiniteMeasure B.cap (B.individual_supported i) hKLimit

lemma poissonCapExcess_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hK : 0<K) (hKLimit : Tendsto Ks atTop (𝓝 K)) :
    Tendsto (fun m => B.poissonCapExcess (Ks m)) atTop (𝓝 (B.poissonCapExcess K)) := by
  have hL : (B.terminal:ℝ)<(K/2:ℝ≥0) := by
    rw [hZero,NNReal.coe_zero]
    exact_mod_cast half_pos hK
  have hNear : ∀ᶠ m in atTop, K/2≤Ks m :=
    (hKLimit.eventually (Ioi_mem_nhds (half_lt_self hK))).mono fun _ h => h.le
  apply tendsto_integral_filter_of_dominated_convergence (fun x => Model.tailValue (K/2) x)
  · exact Eventually.of_forall fun m => (Model.measurable_tailValue (Ks m)).aestronglyMeasurable
  · filter_upwards [hNear] with m hm
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (Model.tailValue_nonnegative (Ks m) x)]
      have hmR : (K/2:ℝ≥0)≤Ks m := hm
      exact max_le_max (sub_le_sub_left (show ((K/2:ℝ≥0):ℝ)≤(Ks m:ℝ) by exact_mod_cast hmR) x) le_rfl
  · exact B.poissonCapExcess_integrable (K/2) hL
  · exact Eventually.of_forall fun x =>
      ((((tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub (NNReal.tendsto_coe.2 hKLimit)).max
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 (0:ℝ)))))

lemma totalCapExcess_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hK : 0<K) (hKLimit : Tendsto Ks atTop (𝓝 K)) :
    Tendsto (fun m => B.totalCapExcess (Ks m)) atTop (𝓝 (B.totalCapExcess K)) := by
  have hL : (B.terminal:ℝ)<(K/2:ℝ≥0) := by rw [hZero,NNReal.coe_zero];exact_mod_cast half_pos hK
  have hNear : ∀ᶠ m in atTop, K/2≤Ks m :=
    (hKLimit.eventually (Ioi_mem_nhds (half_lt_self hK))).mono fun _ h => h.le
  have hSum := tendsto_tsum_of_dominated_convergence (B.summable_individualCapExcess (K/2) hL)
    (fun i => B.individualCapExcess_tendsto hKLimit i) (by
      filter_upwards [hNear] with m hm i
      rw [Real.norm_eq_abs,abs_of_nonneg (B.individualCapExcess_nonnegative (Ks m) i)]
      exact B.individualCapExcess_antitone i hm)
  exact hSum.add (B.poissonCapExcess_tendsto hZero hK hKLimit)

lemma partialCapExcess_tendsto_moving (B : CountableInstance) (hZero : B.terminal=0)
    (Ns : ℕ → ℕ) (hN : Tendsto Ns atTop atTop)
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hK : 0<K) (hKLimit : Tendsto Ks atTop (𝓝 K)) :
    Tendsto (fun m => ∑ i ∈ Finset.range (Ns m), B.individualCapExcess (Ks m) i) atTop
      (𝓝 (∑' i, B.individualCapExcess K i)) := by
  let f := fun m i => if i<Ns m then B.individualCapExcess (Ks m) i else 0
  have hEach (i : ℕ) : Tendsto (fun m => f m i) atTop (𝓝 (B.individualCapExcess K i)) := by
    apply (B.individualCapExcess_tendsto hKLimit i).congr'
    filter_upwards [(tendsto_atTop.1 hN) (i+1)] with m hm
    exact (if_pos (show i<Ns m by omega)).symm
  have hL : (B.terminal:ℝ)<(K/2:ℝ≥0) := by rw [hZero,NNReal.coe_zero];exact_mod_cast half_pos hK
  have hNear : ∀ᶠ m in atTop, K/2≤Ks m :=
    (hKLimit.eventually (Ioi_mem_nhds (half_lt_self hK))).mono fun _ h => h.le
  have hSum := tendsto_tsum_of_dominated_convergence (B.summable_individualCapExcess (K/2) hL) hEach (by
    filter_upwards [hNear] with m hm i
    by_cases hi : i<Ns m
    · simp only [f,if_pos hi,Real.norm_eq_abs,abs_of_nonneg (B.individualCapExcess_nonnegative (Ks m) i)]
      exact B.individualCapExcess_antitone i hm
    · simp only [f,if_neg hi,norm_zero]
      exact B.individualCapExcess_nonnegative (K/2) i)
  have hFinite (m : ℕ) : (∑' i, f m i)=∑ i ∈ Finset.range (Ns m), B.individualCapExcess (Ks m) i := by
    rw [tsum_eq_sum (s:=Finset.range (Ns m))]
    · apply Finset.sum_congr rfl
      intro i hi
      exact if_pos (Finset.mem_range.mp hi)
    · intro i hi
      exact if_neg (by simpa only [Finset.mem_range] using hi)
  have hFun : (fun m => ∑' i, f m i)=(fun m => ∑ i ∈ Finset.range (Ns m), B.individualCapExcess (Ks m) i) := funext hFinite
  rwa [hFun] at hSum

lemma truncation_totalCapExcess (B : CountableInstance) (N : ℕ) {b : ℝ} (hb : (B.terminal:ℝ)<b)
    (K : ℝ≥0) (hbK : b≤(K:ℝ)) :
    (B.truncation N b hb).totalCapExcess K=(∑ i ∈ Finset.range N, B.individualCapExcess K i)+B.poissonCapExcess K := by
  change (∑ i : Fin N, B.individualCapExcess K i.val)+(∫ x, Model.tailValue K x ∂B.intensity.restrict (Ioi b))=_
  rw [Fin.sum_univ_eq_sum_range]
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  unfold Model.tailValue
  apply max_eq_right
  have hxb : x≤b := le_of_not_gt hx
  exact sub_nonpos.mpr (hxb.trans hbK)

lemma truncation_totalCapExcess_tendsto_moving (B : CountableInstance) (hZero : B.terminal=0)
    (Ns : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal:ℝ)<bs m)
    (hN : Tendsto Ns atTop atTop) (hb : Tendsto bs atTop (𝓝 (B.terminal:ℝ)))
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hK : 0<K) (hKLimit : Tendsto Ks atTop (𝓝 K)) :
    Tendsto (fun m => (B.truncation (Ns m) (bs m) (hbs m)).totalCapExcess (Ks m)) atTop (𝓝 (B.totalCapExcess K)) := by
  have hSum := (B.partialCapExcess_tendsto_moving hZero Ns hN hK hKLimit).add
    (B.poissonCapExcess_tendsto hZero hK hKLimit)
  apply hSum.congr'
  have hL : (B.terminal:ℝ)<((K/2:ℝ≥0):ℝ) := by rw [hZero,NNReal.coe_zero];exact_mod_cast half_pos hK
  have hBelow := hb.eventually (Iio_mem_nhds hL)
  have hNear := hKLimit.eventually (Ioi_mem_nhds (half_lt_self hK))
  filter_upwards [hBelow,hNear] with m hm hKm
  exact (B.truncation_totalCapExcess (Ns m) (hbs m) (Ks m) (hm.le.trans (by exact_mod_cast hKm.le))).symm

end ProphetSecretary.Limiting.CountableInstance
