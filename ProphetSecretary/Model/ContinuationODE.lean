import ProphetSecretary.Model.BellmanOptimal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import ProphetSecretary.Model.ScalarEnvelope
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# The remaining-horizon Bellman equation

Regularity is derived from the proved first-arrival Bellman equation. Multiplication by
the positive horizon's cardinality power gives a Volterra integral with continuous child
values. The reward-only value at horizon zero is retained; only its product with that
cardinality power vanishes for a nonempty instance.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace ProphetSecretary.Model

/-- The additional scalar value on remaining horizon `u`, with the policy clock already
normalized to the unit interval. The value at zero is the reward-only stopping value. -/
noncomputable def remainingScalarValue {m : ℕ} (P : Instance m) (w c u : ℝ) : ℝ :=
  optimalScalarValue P w (c * u)

@[simp] lemma remainingScalarValue_zero_horizon {m : ℕ} (P : Instance m) (w c : ℝ) :
    remainingScalarValue P w c 0 = optimalScalarValue P w 0 := by
  simp [remainingScalarValue]

lemma remainingScalarValue_empty (P : Instance 0) (w c u : ℝ) :
    remainingScalarValue P w c u = c * u := optimalScalarValue_empty P w (c * u)

noncomputable def expectedMaxWith (μ : Measure ℝ) (w z : ℝ) : ℝ :=
  ∫ x, max (w * x) z ∂μ

lemma integrable_max_with (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (w z : ℝ) : Integrable (fun x => max (w * x) z) μ :=
  (hμ.const_mul w).sup (integrable_const z)

lemma expectedMaxWith_lipschitz (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (w : ℝ) : LipschitzWith 1 (expectedMaxWith μ w) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro z z'
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  unfold expectedMaxWith
  rw [← integral_sub (integrable_max_with μ hμ w z) (integrable_max_with μ hμ w z')]
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun x => max (w * x) z - max (w * x) z')
    (C := |z - z'|) (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, sub_self, abs_zero, max_eq_right (abs_nonneg (z - z'))] using
        abs_max_sub_max_le_max (w * x) z (w * x) z')
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

lemma expectedMaxWith_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (w : ℝ) : Continuous (expectedMaxWith μ w) :=
  (expectedMaxWith_lipschitz μ hμ w).continuous

lemma remainingScalarValue_continuousOn {m : ℕ} (P : Instance m)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    ContinuousOn (remainingScalarValue P w c) (Ici (0 : ℝ)) :=
  (optimalScalarValue_durationWeight_continuousOn P hP hw).comp
    (continuous_const.mul continuous_id).continuousOn (fun _ hu => mul_nonneg hc hu)

namespace Instance

variable {n : ℕ}

lemma remainingSet_card_eq (i : Fin (n + 1)) : (remainingSet i).card = n := by
  simp [remainingSet]

/-- Candidate's expected acceptance-or-continuation value at a fixed remaining horizon. -/
noncomputable def childMaximum (P : Instance (n + 1)) (i : Fin (n + 1)) (w c u : ℝ) : ℝ :=
  expectedMaxWith (P.law i) w (remainingScalarValue (P.restrictTo (remainingSet i)) w c u)

noncomputable def childMaximumSum (P : Instance (n + 1)) (w c u : ℝ) : ℝ :=
  ∑ i, P.childMaximum i w c u

lemma childMaximum_continuousOn (P : Instance (n + 1)) (hP : Integrable maximum P.valuesLaw)
    (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    ContinuousOn (P.childMaximum i w c) (Ici (0 : ℝ)) :=
  (expectedMaxWith_continuous (P.law i) (P.integrable_maximum_iff.mp hP i) w).comp_continuousOn
    (remainingScalarValue_continuousOn (P.restrictTo (remainingSet i))
      (P.restrictTo_integrable_maximum _ hP) hw hc)

lemma childMaximumSum_continuousOn (P : Instance (n + 1)) (hP : Integrable maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    ContinuousOn (P.childMaximumSum w c) (Ici (0 : ℝ)) := by
  apply continuousOn_finsetSum
  intro i _
  exact P.childMaximum_continuousOn hP i hw hc

/-- Convert the derived first-time measure to its explicit real density. This equality
holds for every integrand; no unproved generator or conditional-density interface is used. -/
lemma integral_firstChildTimeLaw_eq_interval (i : Fin (n + 1)) (f : ℝ → ℝ) :
    (∫ t, f t ∂firstChildTimeLaw i) = ∫ t in (0 : ℝ)..1, (1 - t) ^ n * f t := by
  unfold firstChildTimeLaw
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_firstArrivalDensity _)
    (Eventually.of_forall (fun t => by simp [firstArrivalDensity]))]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [firstArrivalDensity, remainingSet_card_eq, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2), smul_eq_mul]

/-- The actual first-arrival Bellman equation as an ordinary interval integral. -/
lemma remainingScalarValue_eq_interval (P : Instance (n + 1)) (hP : Integrable maximum P.valuesLaw)
    {w c u : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 ≤ u) :
    remainingScalarValue P w c u = ∑ i : Fin (n + 1),
      ∫ t in (0 : ℝ)..1, (1 - t) ^ n *
        (c * u * t + P.childMaximum i w c (u * (1 - t))) := by
  rw [remainingScalarValue, P.optimalScalarValue_eq_bellmanValue hP hw (mul_nonneg hc hu)]
  unfold bellmanValue
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_prod _ (P.integrable_bellmanFirstPayoff hP i hw.le (mul_nonneg hc hu))]
  calc
    (∫ t, ∫ x, P.bellmanFirstPayoff i w (c * u) (t, x) ∂P.law i ∂firstChildTimeLaw i) =
      ∫ t, (c * u * t + expectedMaxWith (P.law i) w (P.bellmanContinuation i w (c * u) t))
        ∂firstChildTimeLaw i := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        change (∫ x, c * u * t + max (w * x) (P.bellmanContinuation i w (c * u) t) ∂P.law i) = _
        rw [integral_add (integrable_const _) (integrable_max_with (P.law i)
          (P.integrable_maximum_iff.mp hP i) w _)]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, expectedMaxWith]
    _ = ∫ t in (0 : ℝ)..1, (1 - t) ^ n *
        (c * u * t + P.childMaximum i w c (u * (1 - t))) := by
      rw [integral_firstChildTimeLaw_eq_interval]
      apply intervalIntegral.integral_congr
      intro t ht
      have h01 : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
      simp only [bellmanContinuation, childMaximum, remainingScalarValue,
        max_eq_right (sub_nonneg.mpr h01.2)]
      simp only [mul_assoc]

/-- Affine change of remaining-time variables, including the zero-horizon identity.
The factor `u^(n+1)` comes from the `n` surviving clocks and the time Jacobian. -/
lemma weighted_remaining_change (n : ℕ) (u : ℝ) (f : ℝ → ℝ) :
    u ^ (n + 1) * (∫ t in (0 : ℝ)..1, (1 - t) ^ n * f (u * (1 - t))) =
      ∫ s in (0 : ℝ)..u, s ^ n * f s := by
  have h := intervalIntegral.smul_integral_comp_sub_mul (a := (0 : ℝ)) (b := 1)
    (fun s : ℝ => s ^ n * f s) u u
  simp only [smul_eq_mul, mul_one, sub_self, mul_zero, sub_zero] at h
  have he : (fun t : ℝ => (u - u * t) ^ n * f (u - u * t)) =
      (fun t => u ^ n * ((1 - t) ^ n * f (u * (1 - t)))) := by
    funext t
    rw [show u - u * t = u * (1 - t) by ring, mul_pow]
    ring
  change u * (∫ t in (0 : ℝ)..1, (u - u * t) ^ n * f (u - u * t)) =
    ∫ s in (0 : ℝ)..u, s ^ n * f s at h
  rw [he, intervalIntegral.integral_const_mul] at h
  simpa only [pow_succ, mul_assoc, mul_comm u] using h

lemma weighted_duration_integral (n : ℕ) (u : ℝ) :
    (n + 1 : ℝ) * (∫ s in (0 : ℝ)..u, s ^ n * (u - s)) = u ^ (n + 2) / (n + 2) := by
  have he : (fun s : ℝ => s ^ n * (u - s)) = (fun s => u * s ^ n - s ^ (n + 1)) := by
    funext s
    rw [pow_succ]
    ring
  have hi1 : IntervalIntegrable (fun s : ℝ => u * s ^ n) volume 0 u :=
    (continuous_const.mul (continuous_id.pow n)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun s : ℝ => s ^ (n + 1)) volume 0 u :=
    (continuous_id.pow (n + 1)).intervalIntegrable _ _
  rw [he, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  simp only [zero_pow (by omega : n + 1 ≠ 0), zero_pow (by omega : n + 1 + 1 ≠ 0), sub_zero]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
  field_simp
  ring

lemma intervalIntegrable_child_power (P : Instance (n + 1)) (hP : Integrable maximum P.valuesLaw)
    (i : Fin (n + 1)) {w c u : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hu : 0 ≤ u) :
    IntervalIntegrable (fun s => s ^ n * P.childMaximum i w c s) volume 0 u := by
  have hcont : ContinuousOn (fun s => s ^ n * P.childMaximum i w c s) (Icc (0 : ℝ) u) :=
    (continuousOn_id.pow n).mul ((P.childMaximum_continuousOn hP i hw hc).mono
      (fun _ hs => hs.1))
  exact hcont.intervalIntegrable_of_Icc hu

/-- The proved Bellman equation in Volterra form. The nonempty instance's value at
zero need not vanish: the factor `u^(n+1)` supplies the boundary cancellation. -/
lemma remainingScalarValue_volterra (P : Instance (n + 1)) (hP : Integrable maximum P.valuesLaw)
    {w c u : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 ≤ u) :
    u ^ (n + 1) * remainingScalarValue P w c u = c * u ^ (n + 2) / (n + 2) +
      ∫ s in (0 : ℝ)..u, s ^ n * P.childMaximumSum w c s := by
  have hI := fun i => P.intervalIntegrable_child_power hP i hw.le hc hu
  have hD : IntervalIntegrable (fun s : ℝ => s ^ n * (c * (u - s))) volume 0 u :=
    ((continuous_id.pow n).mul (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _
  have hDval : (∫ s in (0 : ℝ)..u, s ^ n * (c * (u - s))) =
      c * (∫ s in (0 : ℝ)..u, s ^ n * (u - s)) := by
    have he : (fun s : ℝ => s ^ n * (c * (u - s))) = (fun s => c * (s ^ n * (u - s))) := by
      funext s
      ring
    rw [he, intervalIntegral.integral_const_mul]
  have hsplit (i : Fin (n + 1)) :
      (∫ s in (0 : ℝ)..u, s ^ n * (c * (u - s) + P.childMaximum i w c s)) =
      c * (∫ s in (0 : ℝ)..u, s ^ n * (u - s)) +
        ∫ s in (0 : ℝ)..u, s ^ n * P.childMaximum i w c s := by
    have he : (fun s : ℝ => s ^ n * (c * (u - s) + P.childMaximum i w c s)) =
        (fun s => s ^ n * (c * (u - s)) + s ^ n * P.childMaximum i w c s) := by
      funext s
      ring
    rw [he, intervalIntegral.integral_add hD (hI i), hDval]
  have hSum : (∑ i : Fin (n + 1), ∫ s in (0 : ℝ)..u, s ^ n * P.childMaximum i w c s) =
      ∫ s in (0 : ℝ)..u, s ^ n * P.childMaximumSum w c s := by
    rw [← intervalIntegral.integral_finsetSum (fun i _ => hI i)]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [childMaximumSum, Finset.mul_sum]
  calc
    u ^ (n + 1) * remainingScalarValue P w c u =
        ∑ i : Fin (n + 1), ∫ s in (0 : ℝ)..u, s ^ n * (c * (u - s) + P.childMaximum i w c s) := by
      rw [P.remainingScalarValue_eq_interval hP hw hc hu, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have he : (fun t : ℝ => (1 - t) ^ n * (c * u * t + P.childMaximum i w c (u * (1 - t)))) =
          (fun t => (1 - t) ^ n * ((fun s => c * (u - s) + P.childMaximum i w c s) (u * (1 - t)))) := by
        funext t
        ring
      rw [he]
      exact weighted_remaining_change n u (fun s => c * (u - s) + P.childMaximum i w c s)
    _ = (n + 1 : ℝ) * c * (∫ s in (0 : ℝ)..u, s ^ n * (u - s)) +
        ∫ s in (0 : ℝ)..u, s ^ n * P.childMaximumSum w c s := by
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, hSum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    _ = c * u ^ (n + 2) / (n + 2) + ∫ s in (0 : ℝ)..u, s ^ n * P.childMaximumSum w c s := by
      rw [show (n + 1 : ℝ) * c * (∫ s in (0 : ℝ)..u, s ^ n * (u - s)) =
        c * ((n + 1 : ℝ) * (∫ s in (0 : ℝ)..u, s ^ n * (u - s))) by ring,
        weighted_duration_integral]
      ring

noncomputable def bellmanVolterra (P : Instance (n + 1)) (w c u : ℝ) : ℝ :=
  c * u ^ (n + 2) / (n + 2) + ∫ s in (0 : ℝ)..u, s ^ n * P.childMaximumSum w c s

lemma bellmanVolterra_hasDerivAt (P : Instance (n + 1)) (hP : Integrable maximum P.valuesLaw)
    {w c u : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hu : 0 < u) :
    HasDerivAt (P.bellmanVolterra w c) (c * u ^ (n + 1) + u ^ n * P.childMaximumSum w c u) u := by
  have hcont : ContinuousOn (fun s => s ^ n * P.childMaximumSum w c s) (Ici (0 : ℝ)) :=
    (continuousOn_id.pow n).mul (P.childMaximumSum_continuousOn hP hw hc)
  have hInt : IntervalIntegrable (fun s => s ^ n * P.childMaximumSum w c s) volume 0 u :=
    (hcont.mono (fun _ hs => hs.1)).intervalIntegrable_of_Icc hu.le
  have hMeas : StronglyMeasurableAtFilter (fun s => s ^ n * P.childMaximumSum w c s) (𝓝 u) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi (hcont.mono Ioi_subset_Ici_self) u hu
  have hAt : ContinuousAt (fun s => s ^ n * P.childMaximumSum w c s) u :=
    hcont.continuousAt (Ici_mem_nhds hu)
  have hFTC := intervalIntegral.integral_hasDerivAt_right hInt hMeas hAt
  have hpoly : HasDerivAt (fun v : ℝ => c * v ^ (n + 2) / (n + 2)) (c * u ^ (n + 1)) u := by
    have h := ((hasDerivAt_pow (n + 2) u).const_mul c).div_const (n + 2 : ℝ)
    simp only [Nat.cast_add, Nat.cast_ofNat, show n + 2 - 1 = n + 1 by omega] at h
    have he : c * (((n : ℝ) + 2) * u ^ (n + 1)) / ((n : ℝ) + 2) = c * u ^ (n + 1) := by
      field_simp
    simpa only [he] using h
  exact hpoly.add hFTC

/-- Positive-horizon differentiability follows from the integral equation, rather than
from a postulated arrival-process generator. -/
lemma remainingScalarValue_differentiableAt (P : Instance (n + 1))
    (hP : Integrable maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u) :
    DifferentiableAt ℝ (remainingScalarValue P w c) u := by
  have hF := P.bellmanVolterra_hasDerivAt hP hw.le hc hu
  have hRatio := hF.differentiableAt.div ((differentiableAt_id : DifferentiableAt ℝ id u).pow (n + 1))
    (pow_ne_zero (n + 1) hu.ne')
  apply hRatio.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with v hv
  apply (eq_div_iff (pow_ne_zero (n + 1) hv.ne')).mpr
  simpa only [bellmanVolterra, id_eq, mul_comm] using P.remainingScalarValue_volterra hP hw hc hv.le

/-- Bellman ODE with respect to the remaining horizon. The duration sign is positive;
changing to elapsed time reverses that derivative. -/
theorem remainingScalarValue_ode (P : Instance (n + 1))
    (hP : Integrable maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u) :
    u * deriv (remainingScalarValue P w c) u = c * u +
      ∑ i : Fin (n + 1), (P.childMaximum i w c u - remainingScalarValue P w c u) := by
  have hv := (P.remainingScalarValue_differentiableAt hP hw hc hu).hasDerivAt
  have hp : HasDerivAt (fun v : ℝ => v ^ (n + 1)) ((n + 1 : ℝ) * u ^ n) u := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel_right] using hasDerivAt_pow (n + 1) u
  have hprod := hp.mul hv
  have he : P.bellmanVolterra w c =ᶠ[𝓝 u]
      (fun v => v ^ (n + 1) * remainingScalarValue P w c v) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact (P.remainingScalarValue_volterra hP hw hc hv.le).symm
  have hderiv := (hprod.congr_of_eventuallyEq he).unique (P.bellmanVolterra_hasDerivAt hP hw.le hc hu)
  have hfactor : u ^ n * ((n + 1 : ℝ) * remainingScalarValue P w c u +
      u * deriv (remainingScalarValue P w c) u) = u ^ n * (c * u + P.childMaximumSum w c u) := by
    calc
      _ = ((n + 1 : ℝ) * u ^ n) * remainingScalarValue P w c u +
          u ^ (n + 1) * deriv (remainingScalarValue P w c) u := by rw [pow_succ]; ring
      _ = c * u ^ (n + 1) + u ^ n * P.childMaximumSum w c u := hderiv
      _ = _ := by rw [pow_succ]; ring
  have hcancel := mul_left_cancel₀ (pow_ne_zero n hu.ne') hfactor
  have hsum : (∑ i : Fin (n + 1), (P.childMaximum i w c u - remainingScalarValue P w c u)) =
      P.childMaximumSum w c u - (n + 1 : ℝ) * remainingScalarValue P w c u := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, childMaximumSum]
  rw [hsum]
  linarith

/-- The horizon derivative is continuous at every positive remaining horizon. -/
theorem remainingScalarValue_deriv_continuousOn (P : Instance (n + 1))
    (hP : Integrable maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    ContinuousOn (deriv (remainingScalarValue P w c)) (Ioi (0 : ℝ)) := by
  have hV := (remainingScalarValue_continuousOn P hP hw.le hc).mono Ioi_subset_Ici_self
  have hS := (P.childMaximumSum_continuousOn hP hw.le hc).mono Ioi_subset_Ici_self
  have hcont : ContinuousOn (fun u =>
      (c * u + P.childMaximumSum w c u - (n + 1 : ℝ) * remainingScalarValue P w c u) / u)
      (Ioi (0 : ℝ)) :=
    (((continuousOn_const.mul continuousOn_id).add hS).sub (continuousOn_const.mul hV)).div
      continuousOn_id (fun _ hu => hu.ne')
  apply hcont.congr
  intro u hu
  have h := P.remainingScalarValue_ode hP hw hc hu
  have hsum : (∑ i : Fin (n + 1), (P.childMaximum i w c u - remainingScalarValue P w c u)) =
      P.childMaximumSum w c u - (n + 1 : ℝ) * remainingScalarValue P w c u := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, childMaximumSum]
  rw [hsum] at h
  change deriv (remainingScalarValue P w c) u =
    (c * u + P.childMaximumSum w c u - (n + 1 : ℝ) * remainingScalarValue P w c u) / u
  apply (eq_div_iff hu.ne').mpr
  linarith

end Instance

lemma remainingScalarValue_empty_hasDerivAt (P : Instance 0) (w c u : ℝ) :
    HasDerivAt (remainingScalarValue P w c) c u := by
  have he : remainingScalarValue P w c = (fun u : ℝ => c * u) :=
    funext (remainingScalarValue_empty P w c)
  rw [he]
  simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul c

/-- Both the empty and nonempty finite states are differentiable at positive horizons. -/
lemma remainingScalarValue_differentiableAt_all {m : ℕ} (P : Instance m)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u) :
    DifferentiableAt ℝ (remainingScalarValue P w c) u := by
  cases m with
  | zero => exact (remainingScalarValue_empty_hasDerivAt P w c u).differentiableAt
  | succ n => exact P.remainingScalarValue_differentiableAt hP hw hc hu

/-- The manuscript's `v_A` has the same positive-horizon regularity, with every retained
identity represented by `P.restrictTo A`. -/
lemma Instance.continuationValue_differentiableAt {m : ℕ} (P : Instance m)
    (hP : Integrable Instance.maximum P.valuesLaw) (A : Finset (Fin m)) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u) :
    DifferentiableAt ℝ (fun v => P.continuationValue A v w c) u := by
  exact remainingScalarValue_differentiableAt_all (P.restrictTo A)
    (P.restrictTo_integrable_maximum A hP) hw hc hu

/-- Envelope identity for a fixed policy optimal at the base horizon. The policy is
held fixed when varying the horizon in its affine supporting payoff. -/
lemma remainingScalarValue_deriv_eq_fixedOptimalDuration {m : ℕ} (P : Instance m)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u) (π : RandomizedPolicy m)
    (hopt : π.scalarObjective P w (c * u) = remainingScalarValue P w c u) :
    deriv (remainingScalarValue P w c) u = c * π.expectedDuration P := by
  have h := π.horizon_envelope P hP hw.le hc hu hopt
    (remainingScalarValue_differentiableAt_all P hP hw hc hu)
  exact h.deriv

/-- Canonical-policy specialization discharges optimality using the proved finite
Bellman optimizer, rather than an optimizer field supplied by the caller. -/
lemma remainingScalarValue_deriv_eq_canonicalDuration {m : ℕ} (P : Instance m)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u) :
    deriv (remainingScalarValue P w c) u =
      c * (P.valuePolicy hP hw.le (mul_nonneg hc hu.le)).expectedDuration P :=
  remainingScalarValue_deriv_eq_fixedOptimalDuration P hP hw hc hu _
    (P.valuePolicy_optimal hP hw (mul_nonneg hc hu.le))

lemma remainingScalarValue_hasDerivAt {m : ℕ} (P : Instance m)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u) :
    HasDerivAt (remainingScalarValue P w c)
      (c * (P.valuePolicy hP hw.le (mul_nonneg hc hu.le)).expectedDuration P) u :=
  P.remainingHorizon_envelope hP hw hc hu (remainingScalarValue_differentiableAt_all P hP hw hc hu)

lemma remainingScalarValue_deriv_nonnegative {m : ℕ} (P : Instance m)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u) : 0 ≤ deriv (remainingScalarValue P w c) u := by
  rw [remainingScalarValue_deriv_eq_canonicalDuration P hP hw hc hu]
  exact mul_nonneg hc (RandomizedPolicy.expectedDuration_nonnegative _ P)

lemma remainingScalarValue_deriv_le_durationWeight {m : ℕ} (P : Instance m)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u) : deriv (remainingScalarValue P w c) u ≤ c := by
  rw [remainingScalarValue_deriv_eq_canonicalDuration P hP hw hc hu]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (RandomizedPolicy.expectedDuration_le_one _ P) hc

lemma remainingScalarValue_ode_nonempty {m : ℕ} (P : Instance m) (hm : 0 < m)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u) :
    u * deriv (remainingScalarValue P w c) u = c * u + ∑ i : Fin m,
      (expectedMaxWith (P.law i) w (remainingScalarValue (P.restrictTo (remainingSet i)) w c u) -
        remainingScalarValue P w c u) := by
  cases m with
  | zero => omega
  | succ n => exact P.remainingScalarValue_ode hP hw hc hu

/-- Removing a candidate from the sorted state is exactly erasing its original identity.
This identification is established for the actual scalar values by relabeling policies. -/
lemma Instance.childValue_restrictTo {m : ℕ} (P : Instance m) (A : Finset (Fin m))
    (j : Fin A.card) (hP : Integrable Instance.maximum P.valuesLaw)
    {w d : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d) :
    optimalScalarValue ((P.restrictTo A).restrictTo (remainingSet j)) w d =
      optimalScalarValue (P.restrictTo (A.erase (stateEmbedding A j))) w d := by
  have h := P.optimalScalarValue_restrictTo_map (A.orderEmbOfFin rfl) (remainingSet j) hP hw hd
  have hm : (remainingSet j).map (stateEmbedding A) = A.erase (stateEmbedding A j) := by
    rw [remainingSet, Finset.map_erase]
    exact congrArg (fun B => B.erase (stateEmbedding A j)) (A.map_orderEmbOfFin_univ rfl)
  change optimalScalarValue ((P.restrictTo A).restrictTo (remainingSet j)) w d =
    optimalScalarValue (P.restrictTo ((remainingSet j).map (stateEmbedding A))) w d at h
  rwa [hm] at h

/-- The manuscript's finite state ODE. The sum uses the increasing enumeration of `A`,
and the child erases the corresponding original identity. -/
theorem Instance.continuationValue_ode {m : ℕ} (P : Instance m) (A : Finset (Fin m)) (hA : 0 < A.card)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u) :
    u * deriv (fun v => P.continuationValue A v w c) u = c * u + ∑ j : Fin A.card,
      (expectedMaxWith (P.law (stateEmbedding A j)) w
        (P.continuationValue (A.erase (stateEmbedding A j)) u w c) - P.continuationValue A u w c) := by
  have h := remainingScalarValue_ode_nonempty (P.restrictTo A) hA (P.restrictTo_integrable_maximum A hP) hw hc hu
  change u * deriv (fun v => P.continuationValue A v w c) u = c * u +
    ∑ j : Fin A.card, (expectedMaxWith (P.law (stateEmbedding A j)) w
      (optimalScalarValue ((P.restrictTo A).restrictTo (remainingSet j)) w (c * u)) -
      P.continuationValue A u w c) at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [P.childValue_restrictTo A j hP hw.le (mul_nonneg hc hu.le)]
  rfl

lemma Instance.continuationValue_hasDerivAt {m : ℕ} (P : Instance m) (A : Finset (Fin m))
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 < u) :
    HasDerivAt (fun v => P.continuationValue A v w c)
      (c * ((P.restrictTo A).valuePolicy (P.restrictTo_integrable_maximum A hP) hw.le
        (mul_nonneg hc hu.le)).expectedDuration (P.restrictTo A)) u :=
  remainingScalarValue_hasDerivAt (P.restrictTo A) (P.restrictTo_integrable_maximum A hP) hw hc hu

lemma remainingScalarValue_deriv_continuousOn_all {m : ℕ} (P : Instance m)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    ContinuousOn (deriv (remainingScalarValue P w c)) (Ioi (0 : ℝ)) := by
  cases m with
  | zero =>
    have he : deriv (remainingScalarValue P w c) = (fun _ => c) :=
      funext (fun u => (remainingScalarValue_empty_hasDerivAt P w c u).deriv)
    rw [he]
    exact continuousOn_const
  | succ n => exact P.remainingScalarValue_deriv_continuousOn hP hw hc

lemma Instance.continuationValue_deriv_continuousOn {m : ℕ} (P : Instance m) (A : Finset (Fin m))
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    ContinuousOn (deriv (fun u => P.continuationValue A u w c)) (Ioi (0 : ℝ)) :=
  remainingScalarValue_deriv_continuousOn_all (P.restrictTo A) (P.restrictTo_integrable_maximum A hP) hw hc

/-- On a fixed unseen-state branch, increasing elapsed time decreases continuation.
The canonical policy on the right is fixed at the displayed base remaining horizon. -/
lemma Instance.elapsedContinuation_hasDerivAt {m : ℕ} (P : Instance m) (A : Finset (Fin m))
    (hP : Integrable Instance.maximum P.valuesLaw) {w c t : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (ht : t < 1) :
    HasDerivAt (fun s => P.continuationValue A (1 - s) w c)
      (-(c * ((P.restrictTo A).valuePolicy (P.restrictTo_integrable_maximum A hP) hw.le
        (mul_nonneg hc (sub_pos.mpr ht).le)).expectedDuration (P.restrictTo A))) t := by
  exact HasDerivAt.comp_const_sub 1 t (P.continuationValue_hasDerivAt A hP hw hc (sub_pos.mpr ht))

end ProphetSecretary.Model



