import ProphetSecretary.Model.ConditionalRegret
import ProphetSecretary.Model.BoundaryCharge

/-!
# Conditional finite boundary Hessian

For each fixed residual vector with no endpoint or clock collision, the exact
candidate-clock regret quotient converges to its summed selection charge.
A separate finite-cardinality domination applies to every residual vector.
-/

open MeasureTheory Set Filter
open scoped Classical Topology BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.conditionalDurationRegret_eq_sum (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (π : Policy Unit n)
    (x u : Fin n → ℝ) (i : Fin n) {z z' : ℝ} (hz : 0 < z) (hz' : 0 ≤ z')
    (hInt : ∀ A : Finset (Fin n), Integrable (fun t : ℝ ↦ π.branchMultiplier () x u i A t *
      P.stateBranchLoss hP A z z' (x i) t) volume) :
    P.conditionalDurationRegret π z z' x u i =
      ∑ A : Finset (Fin n), ∫ t : ℝ, π.branchMultiplier () x u i A t *
        P.stateBranchLoss hP A z z' (x i) t := by
  rw [P.conditionalDurationRegret_eq_volume]
  have he : (fun t : ℝ ↦ if t ∈ Icc (0 : ℝ) 1 ∧ t ≤ π.pendingTime () x u i then
      P.durationActionLoss z z' i (x i) u t else 0) =
      (fun t ↦ ∑ A : Finset (Fin n), π.branchMultiplier () x u i A t *
        P.stateBranchLoss hP A z z' (x i) t) := by
    funext t
    exact P.durationLoss_eq_sum_branches hP π x u i hz hz' t
  rw [he, integral_finsetSum Finset.univ (fun A _ ↦ hInt A)]

/-- Exact conditional boundary-Hessian formula. No conditional independence or
survival law is supplied as an assumption: the base pending run is explicit. -/
theorem Instance.conditionalDurationRegret_limit (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z)
    (ω : World n Unit)
    (hr0 : ∀ A : Finset (Fin n),
      (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (ω.1 i) ≠ 0)
    (hru : ∀ (A : Finset (Fin n)) (j : Fin n), j ≠ i →
      (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (ω.1 i) ≠ ω.2.1 j) :
    Tendsto (fun h : ℝ ↦ P.conditionalDurationRegret
      (P.valuePolicy hP zero_le_one hz.le).rule z (z + h) ω.1 ω.2.1 i / h ^ 2)
      (𝓝[≠] 0) (𝓝 ((∑ A : Finset (Fin n), P.crossingSelectionCharge hP i hz (ω.1 i) A ω) / (2 * z))) := by
  let π : Policy Unit n := (P.valuePolicy hP zero_le_one hz.le).rule
  have hSum := tendsto_finsetSum Finset.univ (fun A _ ↦ P.stateBranch_regret_limit hP i hz ω A
    (hr0 A) (hru A))
  have hSum' : Tendsto (fun h : ℝ ↦ ∑ A : Finset (Fin n), (∫ t : ℝ,
      π.branchMultiplier () ω.1 ω.2.1 i A t * P.stateBranchLoss hP A z (z + h) (ω.1 i) t) / h ^ 2)
      (𝓝[≠] 0) (𝓝 ((∑ A : Finset (Fin n), P.crossingSelectionCharge hP i hz (ω.1 i) A ω) / (2 * z))) := by
    convert hSum using 1
    · funext h
      rfl
    · rw [Finset.sum_div]
  apply hSum'.congr'
  have hInts : ∀ᶠ h : ℝ in 𝓝 0, ∀ A : Finset (Fin n), Integrable (fun t : ℝ ↦
      π.branchMultiplier () ω.1 ω.2.1 i A t * P.stateBranchLoss hP A z (z + h) (ω.1 i) t) volume :=
    Filter.eventually_all.mpr (fun A ↦ P.eventually_integrable_stateBranch hP π ω.1 ω.2.1 i A hz
      (hr0 A) (hru A))
  have hc : Continuous (fun h : ℝ ↦ z + h) := continuous_const.add continuous_id
  have hPos : ∀ᶠ h : ℝ in 𝓝 0, 0 < z + h := by
    exact (show Tendsto (fun h : ℝ ↦ z + h) (𝓝 0) (𝓝 z) by simpa only [add_zero] using hc.tendsto 0)
      (Ioi_mem_nhds hz)
  filter_upwards [hInts.filter_mono nhdsWithin_le_nhds, hPos.filter_mono nhdsWithin_le_nhds] with h hI hpos
  rw [P.conditionalDurationRegret_eq_sum hP π ω.1 ω.2.1 i hz hpos.le hI, Finset.sum_div]

/-- A residual-data-uniform bound for dominated convergence. It is preliminary
and depends on finite cardinality; the final charge estimate removes that factor. -/
theorem Instance.eventually_conditionalDurationRegret_bound (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (π : Policy Unit n) {z : ℝ} (hz : 0 < z) :
    ∀ᶠ h : ℝ in 𝓝[≠] 0, ∀ (x u : Fin n → ℝ) (i : Fin n),
      |P.conditionalDurationRegret π z (z + h) x u i / h ^ 2| ≤ 16 * (1 + (n : ℝ)) / z := by
  have hh : ∀ᶠ h : ℝ in 𝓝 0, -z / 2 < h := eventually_gt_nhds (by linarith : -z / 2 < 0)
  filter_upwards [hh.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with h hh hne x u i
  have hn : h ≠ 0 := by simpa using hne
  have hpos : 0 < z + h := by linarith
  have hs : 0 < h ^ 2 := sq_pos_of_ne_zero hn
  have hbound := P.conditionalDurationRegret_le hP π hz.le hpos x u i
  have he : (z - (z + h)) ^ 2 = h ^ 2 := by ring
  rw [he] at hbound
  have hnon := div_nonneg (P.conditionalDurationRegret_nonnegative π z (z + h) x u i) hs.le
  rw [abs_of_nonneg hnon]
  apply (div_le_div_of_nonneg_right hbound hs.le).trans
  have hden : z / 2 ≤ z + h := by linarith
  have hinv := one_div_le_one_div_of_le (by linarith : 0 < z / 2) hden
  calc
    (8 * (1 + (n : ℝ)) * h ^ 2 / (z + h)) / h ^ 2 =
        (8 * (1 + (n : ℝ))) * (1 / (z + h)) := by field_simp [hn, hpos.ne']
    _ ≤ (8 * (1 + (n : ℝ))) * (1 / (z / 2)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by field_simp; ring

end ProphetSecretary.Model
