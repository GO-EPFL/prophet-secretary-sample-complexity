import ProphetSecretary.Reach.TailRounding
import Mathlib.MeasureTheory.Function.Floor

/-!
# The mesh H/m

The downward mesh map preserves zero and the cap exactly. Its error is at most one
mesh width, and its displayed values lie in an explicit finite grid.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Model

noncomputable def meshRound (H : ℝ≥0) (m : ℕ) (x : ℝ) : ℝ :=
  if (H : ℝ) ≤ x then H else ((H : ℝ) / m) * (⌊(m : ℝ) * x / (H : ℝ)⌋₊ : ℝ)

lemma measurable_meshRound (H : ℝ≥0) (m : ℕ) : Measurable (meshRound H m) := by
  have hf : Measurable (fun x : ℝ => (⌊(m : ℝ) * x / (H : ℝ)⌋₊ : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (((measurable_const.mul measurable_id).div_const (H : ℝ)).nat_floor)
  exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const (measurable_const.mul hf)

@[simp] lemma meshRound_cap (H : ℝ≥0) (m : ℕ) : meshRound H m H = (H : ℝ) := by simp [meshRound]

lemma meshRound_bounds (H : ℝ≥0) (hH : (0 : ℝ) < H) (m : ℕ) (hm : 0 < m)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) H) :
    0 ≤ meshRound H m x ∧ meshRound H m x ≤ x ∧ x - meshRound H m x ≤ (H : ℝ) / m := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : (0 : ℝ) < (H : ℝ) / m := div_pos hH hmr
  by_cases hcap : (H : ℝ) ≤ x
  · have hxH : x = (H : ℝ) := le_antisymm hx.2 hcap
    rw [hxH, meshRound_cap]
    exact ⟨H.property, le_rfl, by simpa using hd.le⟩
  · rw [meshRound, if_neg hcap]
    have hnonneg : 0 ≤ (m : ℝ) * x / (H : ℝ) := div_nonneg (mul_nonneg hmr.le hx.1) hH.le
    have hfloor := Nat.floor_le hnonneg
    have hnext := Nat.lt_floor_add_one ((m : ℝ) * x / (H : ℝ))
    have he : ((H : ℝ) / m) * ((m : ℝ) * x / (H : ℝ)) = x := by field_simp
    have hdown := mul_le_mul_of_nonneg_left hfloor hd.le
    have herr := mul_lt_mul_of_pos_left hnext hd
    rw [he] at hdown herr
    refine ⟨mul_nonneg hd.le (Nat.cast_nonneg _), hdown, ?_⟩
    linarith

@[simp] lemma meshRound_zero (H : ℝ≥0) (m : ℕ) : meshRound H m 0 = 0 := by
  by_cases hH : H = 0
  · subst H; simp [meshRound]
  · have hp : (0 : ℝ) < H := by exact_mod_cast (pos_iff_ne_zero.mpr hH)
    simp [meshRound, not_le.mpr hp]

noncomputable def meshGrid (H : ℝ≥0) (m : ℕ) : Finset ℝ :=
  (Finset.range (m + 1)).image (fun k : ℕ => (H : ℝ) / m * k)

lemma zero_mem_meshGrid (H : ℝ≥0) (m : ℕ) : (0 : ℝ) ∈ meshGrid H m := by
  apply Finset.mem_image.mpr
  exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _), by simp⟩

lemma cap_mem_meshGrid (H : ℝ≥0) (m : ℕ) (hm : 0 < m) : (H : ℝ) ∈ meshGrid H m := by
  apply Finset.mem_image.mpr
  refine ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
  have hmr : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  field_simp

lemma meshRound_mem_meshGrid (H : ℝ≥0) (hH : (0 : ℝ) < H) (m : ℕ) (hm : 0 < m)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) H) : meshRound H m x ∈ meshGrid H m := by
  by_cases hcap : (H : ℝ) ≤ x
  · rw [meshRound, if_pos hcap]
    exact cap_mem_meshGrid H m hm
  · have hf : ⌊(m : ℝ) * x / (H : ℝ)⌋₊ ≤ m := by
      apply Nat.floor_le_of_le
      apply (div_le_iff₀ hH).mpr
      exact mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg m)
    apply Finset.mem_image.mpr
    refine ⟨⌊(m : ℝ) * x / (H : ℝ)⌋₊, Finset.mem_range.mpr (Nat.lt_succ_of_le hf), ?_⟩
    simp only [meshRound, if_neg hcap]

namespace Instance

variable {n : ℕ}

/-- The paper's offers `W_i`, on the finite mesh after capping. -/
noncomputable def meshCap (P : Instance n) (H : ℝ≥0) (hH : (0 : ℝ) < H) (m : ℕ) (hm : 0 < m) : Instance n :=
  P.roundedCap H (meshRound H m) (measurable_meshRound H m)
    (fun _ hx => (meshRound_bounds H hH m hm hx).1)

lemma meshCap_values_in_grid (P : Instance n) (H : ℝ≥0) (hH : (0 : ℝ) < H) (m : ℕ) (hm : 0 < m)
    (i : Fin n) : ∀ᵐ x ∂(P.meshCap H hH m hm).law i, x ∈ meshGrid H m := by
  apply (ae_map_iff (measurable_meshRound H m).aemeasurable (meshGrid H m).measurableSet).mpr
  filter_upwards [(P.cap H).nonnegative i, P.cap_bounded H i] with x hx0 hxH
  exact meshRound_mem_meshGrid H hH m hm ⟨hx0, hxH⟩

/-- Equation `upouter:rounding`, including zero and cap atoms. -/
lemma meshCap_expectedMaximum_bounds (P : Instance n) (H : ℝ≥0) (hH : (0 : ℝ) < H) (m : ℕ) (hm : 0 < m) :
    (P.cap H).expectedMaximum - (H : ℝ) / m ≤ (P.meshCap H hH m hm).expectedMaximum ∧
      (P.meshCap H hH m hm).expectedMaximum ≤ (P.cap H).expectedMaximum := by
  exact P.expectedMaximum_rounding_bounds H (meshRound H m) (measurable_meshRound H m)
    (fun _ hx => (meshRound_bounds H hH m hm hx).1)
    (fun _ hx => (meshRound_bounds H hH m hm hx).2.1)
    (div_nonneg H.property (Nat.cast_nonneg m))
    (fun _ hx => (meshRound_bounds H hH m hm hx).2.2)

lemma expectedMaximum_le_meshCap_add_tailSum (P : Instance n) (H : ℝ≥0)
    (hH : (0 : ℝ) < H) (m : ℕ) (hm : 0 < m) (hP : Integrable Instance.maximum P.valuesLaw) :
    P.expectedMaximum ≤ (P.meshCap H hH m hm).expectedMaximum + (H : ℝ) / m + P.tailSum H := by
  have h0 := P.expectedMaximum_le_cap_add_tailSum H hP
  have h1 := (P.meshCap_expectedMaximum_bounds H hH m hm).1
  linarith

end Instance

namespace RandomizedPolicy

variable {n : ℕ}

/-- `upouter:lift-identities` for the actual mesh `H/m`. The policy accepts reached
caps on its displayed instance and receives the original selected offer. -/
lemma mesh_cap_pullback_tail_gain (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0)
    (hH : (0 : ℝ) < H) (m : ℕ) (hm : 0 < m)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (hacc : ∀ᵐ ω : π.World ∂(P.meshCap H hH m hm).worldLaw π.seedLaw,
      π.rule.AcceptsReachedCap H ω.2.2 ω.1 ω.2.1) :
    π.expectedReward (P.meshCap H hH m hm) +
      ∑ i, π.rule.reachProbability (P.meshCap H hH m hm) π.seedLaw i * ∫ x, tailValue H x ∂P.law i ≤
        ((π.pullbackValues (meshRound H m) (measurable_meshRound H m)).pullbackValues
          (capValue H) (measurable_capValue H)).expectedReward P := by
  exact π.rounded_cap_pullback_tail_gain P H hP (meshRound H m) (measurable_meshRound H m)
    (fun _ hx => (meshRound_bounds H hH m hm hx).1)
    (fun _ hx => (meshRound_bounds H hH m hm hx).2.1) (meshRound_cap H m) hacc


/-- `upouter:lift-conclusion`. Inner training and independent randomization are
included in the policy's seed law; the outer-pilot-selected cap and mesh are fixed here. -/
lemma mesh_cap_pullback_reward_guarantee (π : RandomizedPolicy n) (P : Instance n) (H : ℝ≥0)
    (hH : (0 : ℝ) < H) (m : ℕ) (hm : 0 < m) (hP : Integrable Instance.maximum P.valuesLaw)
    (hacc : ∀ᵐ ω : π.World ∂(P.meshCap H hH m hm).worldLaw π.seedLaw,
      π.rule.AcceptsReachedCap H ω.2.2 ω.1 ω.2.1)
    {rho Delta : ℝ} (hrho : 0 ≤ rho)
    (hR : rho * (P.meshCap H hH m hm).expectedMaximum - Delta ≤ π.expectedReward (P.meshCap H hH m hm))
    (hq : ∀ i, rho ≤ π.rule.reachProbability (P.meshCap H hH m hm) π.seedLaw i) :
    rho * P.expectedMaximum - Delta - rho * ((H : ℝ) / m) ≤
      ((π.pullbackValues (meshRound H m) (measurable_meshRound H m)).pullbackValues
        (capValue H) (measurable_capValue H)).expectedReward P := by
  exact π.rounded_cap_pullback_reward_guarantee P H hP (meshRound H m) (measurable_meshRound H m)
    (fun _ hx => (meshRound_bounds H hH m hm hx).1)
    (fun _ hx => (meshRound_bounds H hH m hm hx).2.1) (meshRound_cap H m)
    (div_nonneg H.property (Nat.cast_nonneg m))
    (fun _ hx => (meshRound_bounds H hH m hm hx).2.2) hacc hrho hR hq

end RandomizedPolicy

end ProphetSecretary.Model
