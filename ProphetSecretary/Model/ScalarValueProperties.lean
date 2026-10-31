import ProphetSecretary.Model.ScalarObjectiveBounds
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact

/-!
# Elementary regularity of the optimal scalar value

The optimal value is a supremum over all admissible randomized policies. These
arguments use only bounded expectations and do not assume an optimizer exists.
They distinguish linearity for a fixed policy from convexity after reoptimization.
-/

open MeasureTheory Set
open scoped NNReal

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- Increasing either nonnegative coefficient cannot decrease a fixed policy's payoff. -/
theorem RandomizedPolicy.scalarObjective_mono (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c w' c' : ℝ}
    (hw : w ≤ w') (hc : c ≤ c') :
    π.scalarObjective P w c ≤ π.scalarObjective P w' c' := by
  rw [π.scalarObjective_eq P hP, π.scalarObjective_eq P hP]
  exact add_le_add (mul_le_mul_of_nonneg_right hw (π.expectedReward_nonnegative P))
    (mul_le_mul_of_nonneg_right hc (π.expectedDuration_nonnegative P))

/-- Monotonicity of the optimized value, without choosing an optimizer. -/
theorem optimalScalarValue_mono (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c w' c' : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hw' : w ≤ w') (hc' : c ≤ c') :
    optimalScalarValue P w c ≤ optimalScalarValue P w' c' := by
  apply csSup_le (scalarValues_nonempty P w c)
  rintro v ⟨π, rfl⟩
  exact (π.scalarObjective_mono P hP hw' hc').trans
    (scalarObjective_le_optimal π P hP (hw.trans hw') (hc.trans hc'))

/-- Positive homogeneity of `V(P;w,c)`. No optimal policy is assumed. -/
theorem optimalScalarValue_smul (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a w c : ℝ}
    (ha : 0 ≤ a) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue P (a * w) (a * c) = a * optimalScalarValue P w c := by
  have hupper : optimalScalarValue P (a * w) (a * c) ≤ a * optimalScalarValue P w c := by
    apply csSup_le (scalarValues_nonempty P (a * w) (a * c))
    rintro v ⟨π, rfl⟩
    rw [π.scalarObjective_smul P hP]
    exact mul_le_mul_of_nonneg_left (scalarObjective_le_optimal π P hP hw hc) ha
  apply le_antisymm hupper
  by_cases ha0 : a = 0
  · subst a
    simpa using optimalScalarValue_nonnegative P hP (w := 0) (c := 0) le_rfl le_rfl
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hlower : optimalScalarValue P w c ≤ optimalScalarValue P (a * w) (a * c) / a := by
    apply csSup_le (scalarValues_nonempty P w c)
    rintro v ⟨π, rfl⟩
    apply (le_div_iff₀ hapos).mpr
    have h := scalarObjective_le_optimal π P hP (mul_nonneg ha hw) (mul_nonneg ha hc)
    rw [π.scalarObjective_smul P hP] at h
    simpa only [mul_comm] using h
  have h := (le_div_iff₀ hapos).mp hlower
  simpa only [mul_comm] using h

/-- The fixed-policy normalized objective is affine in its weight. -/
theorem RandomizedPolicy.scalarObjective_weight_affine (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (x y a b : ℝ) (hab : a + b = 1) :
    π.scalarObjective P (a * x + b * y) (1 - (a * x + b * y)) =
      a * π.scalarObjective P x (1 - x) + b * π.scalarObjective P y (1 - y) := by
  rw [π.scalarObjective_eq P hP, π.scalarObjective_eq P hP, π.scalarObjective_eq P hP]
  have hb : b = 1 - a := by linarith
  rw [hb]
  ring

/-- Reoptimization makes the normalized scalar value convex on `[0,1]`. -/
theorem optimalScalarValue_weight_convex (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun lam ↦ optimalScalarValue P lam (1 - lam)) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  apply csSup_le (scalarValues_nonempty P (a * x + b * y) (1 - (a * x + b * y)))
  rintro v ⟨π, rfl⟩
  rw [π.scalarObjective_weight_affine P hP x y a b hab]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (scalarObjective_le_optimal π P hP hx.1 (sub_nonneg.mpr hx.2)) ha)
    (mul_le_mul_of_nonneg_left (scalarObjective_le_optimal π P hP hy.1 (sub_nonneg.mpr hy.2)) hb)

/-- A fixed policy's normalized reward--duration slope is uniformly bounded. -/
theorem RandomizedPolicy.reward_duration_slope_bound (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    |π.expectedReward P - π.expectedDuration P| ≤ P.expectedMaximum + 1 := by
  rw [abs_le]
  have hR0 := π.expectedReward_nonnegative P
  have hRM := π.expectedReward_le_maximum P hP
  have hT0 := π.expectedDuration_nonnegative P
  have hT1 := π.expectedDuration_le_one P
  have hM0 := P.expectedMaximum_nonnegative
  constructor <;> linarith

/-- The expected payoff of one fixed policy is Lipschitz in normalized weights. -/
theorem RandomizedPolicy.scalarObjective_weight_lipschitz (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (lam rho : ℝ) :
    |π.scalarObjective P lam (1 - lam) - π.scalarObjective P rho (1 - rho)| ≤
      (P.expectedMaximum + 1) * |lam - rho| := by
  have heq : π.scalarObjective P lam (1 - lam) - π.scalarObjective P rho (1 - rho) =
      (lam - rho) * (π.expectedReward P - π.expectedDuration P) := by
    rw [π.scalarObjective_eq P hP, π.scalarObjective_eq P hP]
    ring
  rw [heq, abs_mul, mul_comm (P.expectedMaximum + 1)]
  exact mul_le_mul_of_nonneg_left (π.reward_duration_slope_bound P hP) (abs_nonneg _)

/-- The Lipschitz constant is independent of the number of offers. The expected
maximum is retained explicitly; boundedness of the offers is not required. -/
theorem optimalScalarValue_weight_lipschitz (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam rho : ℝ}
    (hlam : lam ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 1) :
    |optimalScalarValue P lam (1 - lam) - optimalScalarValue P rho (1 - rho)| ≤
      (P.expectedMaximum + 1) * |lam - rho| := by
  have hcross (x y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      optimalScalarValue P x (1 - x) ≤ optimalScalarValue P y (1 - y) +
        (P.expectedMaximum + 1) * |x - y| := by
    apply csSup_le (scalarValues_nonempty P x (1 - x))
    rintro v ⟨π, rfl⟩
    have h := (abs_le.mp (π.scalarObjective_weight_lipschitz P hP x y)).2
    have hv := scalarObjective_le_optimal π P hP hy.1 (sub_nonneg.mpr hy.2)
    linarith
  have h1 := hcross lam rho hrho
  have h2 := hcross rho lam hlam
  rw [abs_sub_comm rho lam] at h2
  rw [abs_le]
  constructor <;> linarith

/-- Changing arbitrary real scalar coefficients for a fixed policy has a
reward error controlled by `M` and a duration error controlled by one. -/
theorem RandomizedPolicy.scalarObjective_coefficients_lipschitz
    (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (w c w' c' : ℝ) :
    |π.scalarObjective P w c - π.scalarObjective P w' c'| ≤
      P.expectedMaximum * |w - w'| + |c - c'| := by
  have heq : π.scalarObjective P w c - π.scalarObjective P w' c' =
      (w - w') * π.expectedReward P + (c - c') * π.expectedDuration P := by
    rw [π.scalarObjective_eq P hP, π.scalarObjective_eq P hP]
    ring
  rw [heq]
  calc
    _ ≤ |(w - w') * π.expectedReward P| + |(c - c') * π.expectedDuration P| := abs_add_le _ _
    _ = |w - w'| * π.expectedReward P + |c - c'| * π.expectedDuration P := by
      rw [abs_mul, abs_mul, abs_of_nonneg (π.expectedReward_nonnegative P),
        abs_of_nonneg (π.expectedDuration_nonnegative P)]
    _ ≤ |w - w'| * P.expectedMaximum + |c - c'| * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (π.expectedReward_le_maximum P hP) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (π.expectedDuration_le_one P) (abs_nonneg _))
    _ = _ := by ring

/-- Uniform continuity in both nonnegative coefficients. This bound is over
the complete admissible policy class and does not require an optimizer. -/
theorem optimalScalarValue_coefficients_lipschitz (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c w' c' : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hw' : 0 ≤ w') (hc' : 0 ≤ c') :
    |optimalScalarValue P w c - optimalScalarValue P w' c'| ≤
      P.expectedMaximum * |w - w'| + |c - c'| := by
  have hcross (a b a' b' : ℝ) (ha' : 0 ≤ a') (hb' : 0 ≤ b') :
      optimalScalarValue P a b ≤ optimalScalarValue P a' b' +
        (P.expectedMaximum * |a - a'| + |b - b'|) := by
    apply csSup_le (scalarValues_nonempty P a b)
    rintro v ⟨π, rfl⟩
    have h := (abs_le.mp (π.scalarObjective_coefficients_lipschitz P hP a b a' b')).2
    have hv := scalarObjective_le_optimal π P hP ha' hb'
    linarith
  have h1 := hcross w c w' c' hw' hc'
  have h2 := hcross w' c' w c hw hc
  rw [abs_sub_comm w' w, abs_sub_comm c' c] at h2
  rw [abs_le]
  constructor <;> linarith

/-- With the reward coefficient fixed, changing duration's coefficient has
Lipschitz constant one, independently of the instance and its number of offers. -/
theorem optimalScalarValue_durationWeight_lipschitz (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c d : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    |optimalScalarValue P w c - optimalScalarValue P w d| ≤ |c - d| := by
  simpa only [sub_self, abs_zero, mul_zero, zero_add] using
    optimalScalarValue_coefficients_lipschitz P hP hw hc hw hd

/-- Rescaling the remaining horizon changes only duration's coefficient in
`v_A(u;w,c)=V(P_A;w,cu)`, and has uniform Lipschitz constant `c`. -/
theorem optimalScalarValue_horizon_lipschitz (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u v : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |optimalScalarValue P w (c * u) - optimalScalarValue P w (c * v)| ≤ c * |u - v| := by
  have h := optimalScalarValue_durationWeight_lipschitz P hP hw
    (mul_nonneg hc hu) (mul_nonneg hc hv)
  simpa only [← mul_sub, abs_mul, abs_of_nonneg hc] using h

/-- The paper's conversion between the `R+zτ` and normalized objectives. -/
theorem optimalScalarValue_normalize (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 ≤ z) :
    optimalScalarValue P (1 / (1 + z)) (z / (1 + z)) =
      (1 / (1 + z)) * optimalScalarValue P 1 z := by
  have h := optimalScalarValue_smul P hP (a := 1 / (1 + z))
    (by positivity) (by norm_num : (0 : ℝ) ≤ 1) hz
  simpa [div_eq_mul_inv, mul_comm] using h

/-- The gap at the global competitive ratio has the same positive homogeneity;
this statement does not assume a numerical bound on that ratio. -/
theorem scalarGap_smul (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a w c : ℝ}
    (ha : 0 ≤ a) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    scalarGap P (a * w) (a * c) = a * scalarGap P w c := by
  unfold scalarGap
  rw [optimalScalarValue_smul P hP ha hw hc]
  ring

/-- Continuity needed when moving tail mass into the duration coefficient. -/
theorem optimalScalarValue_durationWeight_continuousOn (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w : ℝ} (hw : 0 ≤ w) :
    ContinuousOn (fun c ↦ optimalScalarValue P w c) (Ici (0 : ℝ)) := by
  have hLip : LipschitzOnWith 1 (fun c ↦ optimalScalarValue P w c) (Ici (0 : ℝ)) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro c hc d hd
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      optimalScalarValue_durationWeight_lipschitz P hP hw hc hd
  exact hLip.continuousOn

/-- The normalized optimal value is continuous, uniformly in the instance size. -/
theorem optimalScalarValue_weight_continuousOn (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    ContinuousOn (fun lam ↦ optimalScalarValue P lam (1 - lam)) (Icc (0 : ℝ) 1) := by
  let K : ℝ≥0 := ⟨P.expectedMaximum + 1, by linarith [P.expectedMaximum_nonnegative]⟩
  have hLip : LipschitzOnWith K (fun lam ↦ optimalScalarValue P lam (1 - lam))
      (Icc (0 : ℝ) 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro lam hlam rho hrho
    exact optimalScalarValue_weight_lipschitz P hP hlam hrho
  exact hLip.continuousOn

/-- Continuity of the gap does not need an external numerical bound on `C_PS`. -/
theorem normalizedScalarGap_continuousOn (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    ContinuousOn (normalizedScalarGap P) (Icc (0 : ℝ) 1) := by
  unfold normalizedScalarGap scalarGap
  exact (optimalScalarValue_weight_continuousOn P hP).sub
    (continuous_const.mul ((continuous_id.mul continuous_const).add
      (continuous_const.sub continuous_id))).continuousOn

/-- A normalized scalar target minimizing the gap exists. This optimizes only
the coefficient; it does not assert existence of an optimal online policy. -/
theorem normalizedScalarGap_exists_minimizer (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    ∃ lam ∈ Icc (0 : ℝ) 1, ∀ rho ∈ Icc (0 : ℝ) 1,
      normalizedScalarGap P lam ≤ normalizedScalarGap P rho := by
  obtain ⟨lam, hlam, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)) (normalizedScalarGap_continuousOn P hP)
  exact ⟨lam, hlam, hmin⟩

end ProphetSecretary.Model
