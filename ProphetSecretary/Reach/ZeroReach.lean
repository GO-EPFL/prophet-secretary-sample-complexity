import ProphetSecretary.Reach.FiniteReach
import Mathlib.Tactic.Linarith

/-!
# Zero-offer reach and empirical clock discrepancy

For any online policy, the fraction of appended identities reached is exactly their
empirical arrival CDF at the stopping time. This identity retains every zero identity
and permits arbitrary dependence of the policy on its observed history. The discrepancy
below is a measurable finite maximum of right and left empirical-CDF errors.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Reach.ZeroReach

variable {N : ℕ}

noncomputable def empiricalCDF (z : Fin N → ℝ) (t : ℝ) : ℝ :=
  (∑ j : Fin N, if z j ≤ t then (1 : ℝ) else 0) / N

noncomputable def empiricalCDFLeft (z : Fin N → ℝ) (t : ℝ) : ℝ :=
  (∑ j : Fin N, if z j < t then (1 : ℝ) else 0) / N

theorem empiricalCDF_nonnegative (z : Fin N → ℝ) (t : ℝ) : 0 ≤ empiricalCDF z t := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem empiricalCDF_le_one (hN : 0 < N) (z : Fin N → ℝ) (t : ℝ) :
    empiricalCDF z t ≤ 1 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_one hNp).mpr
  calc
    (∑ j : Fin N, if z j ≤ t then (1 : ℝ) else 0) ≤ ∑ _ : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> norm_num
    _ = N := by simp

theorem empiricalCDF_eq_zero (z : Fin N → ℝ) (t : ℝ) (h : ∀ j, ¬z j ≤ t) :
    empiricalCDF z t = 0 := by simp [empiricalCDF, h]

theorem empiricalCDF_eq_one (hN : 0 < N) (z : Fin N → ℝ) (t : ℝ) (h : ∀ j, z j ≤ t) :
    empiricalCDF z t = 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp [empiricalCDF, h, hn]

/-- Right and left errors at each observed clock, and a zero sentinel. -/
noncomputable def candidateError (z : Fin N → ℝ) : Option (Fin N × Bool) → ℝ
  | none => 0
  | some (j, false) => empiricalCDF z (z j) - z j
  | some (j, true) => z j - empiricalCDFLeft z (z j)

noncomputable def rawDiscrepancy (z : Fin N → ℝ) : ℝ :=
  Finset.univ.sup' ⟨none, Finset.mem_univ _⟩ (candidateError z)

/-- Capping at one makes this random variable globally bounded, even outside the support
of the uniform clock law. On valid clocks it dominates every empirical-CDF error. -/
noncomputable def discrepancy (z : Fin N → ℝ) : ℝ := min 1 (rawDiscrepancy z)

theorem rawDiscrepancy_nonnegative (z : Fin N → ℝ) : 0 ≤ rawDiscrepancy z := by
  exact Finset.le_sup' (candidateError z) (Finset.mem_univ none)

theorem rightError_le (z : Fin N → ℝ) (j : Fin N) :
    empiricalCDF z (z j) - z j ≤ rawDiscrepancy z :=
  Finset.le_sup' (candidateError z) (Finset.mem_univ (some (j, false)))

theorem leftError_le (z : Fin N → ℝ) (j : Fin N) :
    z j - empiricalCDFLeft z (z j) ≤ rawDiscrepancy z :=
  Finset.le_sup' (candidateError z) (Finset.mem_univ (some (j, true)))

theorem discrepancy_nonnegative (z : Fin N → ℝ) : 0 ≤ discrepancy z :=
  le_min zero_le_one (rawDiscrepancy_nonnegative z)

theorem discrepancy_le_one (z : Fin N → ℝ) : discrepancy z ≤ 1 := min_le_left _ _

theorem empiricalCDF_sub_le_raw (z : Fin N → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    empiricalCDF z t - t ≤ rawDiscrepancy z := by
  let A := Finset.univ.filter fun j => z j ≤ t
  by_cases hA : A.Nonempty
  · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image A z hA
    have hit : z i ≤ t := (Finset.mem_filter.mp hi).2
    have he : empiricalCDF z t = empiricalCDF z (z i) := by
      unfold empiricalCDF
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have hj : z j ≤ t ↔ z j ≤ z i :=
        ⟨fun h => hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩), fun h => h.trans hit⟩
      simp only [hj]
    rw [he]
    exact (sub_le_sub_left hit _).trans (rightError_le z i)
  · have he : empiricalCDF z t = 0 := by
      apply empiricalCDF_eq_zero
      intro j hj
      exact hA ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    rw [he]
    exact (sub_nonpos.mpr ht).trans (rawDiscrepancy_nonnegative z)

theorem sub_empiricalCDF_le_raw (hN : 0 < N) (z : Fin N → ℝ) {t : ℝ} (ht : t ≤ 1) :
    t - empiricalCDF z t ≤ rawDiscrepancy z := by
  let A := Finset.univ.filter fun j => t < z j
  by_cases hA : A.Nonempty
  · obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image A z hA
    have hti : t < z i := (Finset.mem_filter.mp hi).2
    have he : empiricalCDF z t = empiricalCDFLeft z (z i) := by
      unfold empiricalCDF empiricalCDFLeft
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have hj : z j ≤ t ↔ z j < z i := by
        refine ⟨fun h => h.trans_lt hti, ?_⟩
        intro h
        by_contra h'
        have hji := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h'⟩)
        exact (not_le_of_gt h) hji
      simp only [hj]
    rw [he]
    exact (sub_le_sub_right hti.le _).trans (leftError_le z i)
  · have he : empiricalCDF z t = 1 := by
      apply empiricalCDF_eq_one hN
      intro j
      by_contra hj
      exact hA ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hj⟩⟩
    rw [he]
    exact (sub_nonpos.mpr ht).trans (rawDiscrepancy_nonnegative z)

theorem abs_empiricalCDF_sub_le (hN : 0 < N) (z : Fin N → ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |empiricalCDF z t - t| ≤ discrepancy z := by
  apply le_min
  · apply abs_le.mpr
    constructor <;> linarith [empiricalCDF_nonnegative z t, empiricalCDF_le_one hN z t]
  · apply abs_le.mpr
    constructor
    · have h := sub_empiricalCDF_le_raw hN z ht1
      linarith
    · exact empiricalCDF_sub_le_raw z ht0

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_empiricalCDF {z : Ω → Fin N → ℝ} {t : Ω → ℝ}
    (hz : ∀ j, Measurable fun ω => z ω j) (ht : Measurable t) :
    Measurable fun ω => empiricalCDF (z ω) (t ω) := by
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_le (hz j) ht) measurable_const measurable_const

theorem measurable_empiricalCDFLeft {z : Ω → Fin N → ℝ} {t : Ω → ℝ}
    (hz : ∀ j, Measurable fun ω => z ω j) (ht : Measurable t) :
    Measurable fun ω => empiricalCDFLeft (z ω) (t ω) := by
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_lt (hz j) ht) measurable_const measurable_const

theorem measurable_discrepancy {z : Ω → Fin N → ℝ}
    (hz : ∀ j, Measurable fun ω => z ω j) : Measurable fun ω => discrepancy (z ω) := by
  change Measurable fun ω => min (1 : ℝ) (rawDiscrepancy (z ω))
  apply measurable_const.min
  have h : Measurable ((Finset.univ : Finset (Option (Fin N × Bool))).sup'
      ⟨none, Finset.mem_univ _⟩ (fun j => fun ω => candidateError (z ω) j)) := by
    apply Finset.measurable_sup'
    intro j _
    cases j with
    | none => exact measurable_const
    | some j =>
      rcases j with ⟨j, b⟩
      cases b with
      | false => exact (measurable_empiricalCDF hz (hz j)).sub (hz j)
      | true => exact (hz j).sub (measurable_empiricalCDFLeft hz (hz j))
  convert h using 1
  funext ω
  exact (Finset.sup'_apply (s := (Finset.univ : Finset (Option (Fin N × Bool))))
    ⟨none, Finset.mem_univ _⟩ (fun j => fun ω => candidateError (z ω) j) ω).symm

theorem integrable_discrepancy (μ : Measure Ω) [IsFiniteMeasure μ]
    {z : Ω → Fin N → ℝ} (hz : ∀ j, Measurable fun ω => z ω j) :
    Integrable (fun ω => discrepancy (z ω)) μ := by
  apply Integrable.of_bound (measurable_discrepancy hz).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (discrepancy_nonnegative _)] using discrepancy_le_one (z ω)

/-- The empirical CDF may be evaluated at an arbitrary data-dependent time. No
independence between that time and the observed clocks is required. -/
theorem integral_time_ge_average_reach_sub_discrepancy (hN : 0 < N)
    (μ : Measure Ω) [IsFiniteMeasure μ] {z : Ω → Fin N → ℝ} {t : Ω → ℝ}
    (hz : ∀ j, Measurable fun ω => z ω j) (ht : Measurable t)
    (hunit : ∀ᵐ ω ∂μ, 0 ≤ t ω ∧ t ω ≤ 1) :
    (∑ j : Fin N, μ.real {ω | z ω j ≤ t ω}) / N -
      (∫ ω, discrepancy (z ω) ∂μ) ≤ ∫ ω, t ω ∂μ := by
  have hi : ∀ j : Fin N, Integrable (fun ω => if z ω j ≤ t ω then (1 : ℝ) else 0) μ := by
    intro j
    apply Integrable.of_bound
      (Measurable.ite (measurableSet_le (hz j) ht) measurable_const measurable_const).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω => by split_ifs <;> norm_num
  have hc : Integrable (fun ω => empiricalCDF (z ω) (t ω)) μ := by
    apply Integrable.of_bound (measurable_empiricalCDF hz ht).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (empiricalCDF_nonnegative _ _)] using
        empiricalCDF_le_one hN (z ω) (t ω)
  have hit : Integrable t μ := by
    apply Integrable.of_bound ht.aestronglyMeasurable 1
    filter_upwards [hunit] with ω hω
    simpa [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2
  have hd := integrable_discrepancy μ hz
  have he : (∫ ω, empiricalCDF (z ω) (t ω) ∂μ) =
      (∑ j : Fin N, μ.real {ω | z ω j ≤ t ω}) / N := by
    unfold empiricalCDF
    rw [integral_div, integral_finsetSum _ (fun j _ => hi j)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using
      (integral_indicator_one (μ := μ) (measurableSet_le (hz j) ht))
  have hcomp : (∫ ω, empiricalCDF (z ω) (t ω) ∂μ) ≤
      ∫ ω, t ω + discrepancy (z ω) ∂μ := by
    apply integral_mono_ae hc (hit.add hd)
    filter_upwards [hunit] with ω hω
    change empiricalCDF (z ω) (t ω) ≤ t ω + discrepancy (z ω)
    have h := abs_empiricalCDF_sub_le hN (z ω) hω.1 hω.2
    linarith [le_abs_self (empiricalCDF (z ω) (t ω) - t ω)]
  rw [he, integral_add hit hd] at hcomp
  linarith

end ProphetSecretary.Reach.ZeroReach

namespace ProphetSecretary.Model

open ProphetSecretary.Reach.ZeroReach

variable {Seed : Type*} {n N : ℕ}

/-- The exact fraction of appended identities reached. The definition includes the
stopping identity, as in the manuscript's reach event. -/
noncomputable def Policy.zeroReachFraction (π : Policy Seed (n + N)) (r : Seed)
    (x u : Fin (n + N) → ℝ) : ℝ :=
  (∑ j : Fin N, if π.Reaches r x u (Fin.natAdd n j) then (1 : ℝ) else 0) / N

theorem Policy.zeroReachFraction_eq_empiricalCDF (π : Policy Seed (n + N)) (r : Seed)
    (x u : Fin (n + N) → ℝ) :
    π.zeroReachFraction r x u = empiricalCDF (fun j : Fin N => u (Fin.natAdd n j))
      (π.stoppingTime r Finset.univ x u) := rfl

theorem Policy.abs_zeroReachFraction_sub_duration_le (π : Policy Seed (n + N))
    (hN : 0 < N) (r : Seed) (x u : Fin (n + N) → ℝ) (hu : ∀ i, 0 ≤ u i) :
    |π.zeroReachFraction r x u - π.stoppingTime r Finset.univ x u| ≤
      discrepancy (fun j : Fin N => u (Fin.natAdd n j)) := by
  rw [π.zeroReachFraction_eq_empiricalCDF]
  exact abs_empiricalCDF_sub_le hN _ (π.stoppingTime_nonneg r _ x u hu)
    (π.stoppingTime_le_one r _ x u)

variable [MeasurableSpace Seed]

/-- Policy-uniform expected zero-reach comparison. The discrepancy depends only on
zero clocks; its inverse-square-root expectation estimate is a separate probability bound. -/
theorem Policy.meanDuration_ge_average_zeroReach_sub_discrepancy
    (π : Policy Seed (n + N)) (hπ : π.IsMeasurable) (hN : 0 < N)
    (P : Instance (n + N)) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∑ j : Fin N, π.reachProbability P ν (Fin.natAdd n j)) / N -
      (∫ ω : World (n + N) Seed,
        discrepancy (fun j : Fin N => ω.2.1 (Fin.natAdd n j)) ∂P.worldLaw ν) ≤
      π.meanDuration P ν := by
  exact integral_time_ge_average_reach_sub_discrepancy hN (P.worldLaw ν)
    (fun j => (measurable_pi_apply (Fin.natAdd n j)).comp measurable_snd.fst)
    (π.measurable_worldTime hπ Finset.univ)
    (P.worldTime_mem_unitInterval ν π Finset.univ)

theorem Policy.meanDuration_ge_common_zeroReach_sub_discrepancy
    (π : Policy Seed (n + N)) (hπ : π.IsMeasurable) (hN : 0 < N)
    (P : Instance (n + N)) (ν : Measure Seed) [IsProbabilityMeasure ν] (ρ : ℝ)
    (hq : ∀ j : Fin N, ρ ≤ π.reachProbability P ν (Fin.natAdd n j)) :
    ρ - (∫ ω : World (n + N) Seed,
      discrepancy (fun j : Fin N => ω.2.1 (Fin.natAdd n j)) ∂P.worldLaw ν) ≤
        π.meanDuration P ν := by
  have hsum : (N : ℝ) * ρ ≤ ∑ j : Fin N, π.reachProbability P ν (Fin.natAdd n j) := by
    simpa using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => hq j)
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have havg : ρ ≤ (∑ j : Fin N, π.reachProbability P ν (Fin.natAdd n j)) / N :=
    (le_div_iff₀ hp).mpr (by simpa [mul_comm] using hsum)
  have h := π.meanDuration_ge_average_zeroReach_sub_discrepancy hπ hN P ν
  linarith

end ProphetSecretary.Model
