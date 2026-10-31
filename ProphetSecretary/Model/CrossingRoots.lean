import ProphetSecretary.Model.ThresholdVariation
import ProphetSecretary.Model.ContinuationODE
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Deterministic roots of finite continuation states

For reward-normalized value `f_A(d)=V(P_A;1,d)`, a level `x` above its
reward-only value has a unique positive duration coefficient `d_A(x)`.
A continuous crossing for `R+zτ` then occurs at elapsed time
`1-d_A(x)/z`. The root coefficient is independent of the scalar weight.
-/

open MeasureTheory Set
open scoped Topology NNReal

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.rewardNormalized_strictMonoOn (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    StrictMonoOn (fun d ↦ optimalScalarValue P 1 d) (Ici (0 : ℝ)) := by
  intro d hd e _he hde
  have h := P.remainingHorizon_growth hP (w := 1) (c := 1) zero_lt_one zero_le_one hd hde.le
  have hp : 0 < (1 / (4 * (1 + (n : ℝ)))) * (e - d) :=
    mul_pos (by positivity) (sub_pos.mpr hde)
  simp only [one_mul] at h
  linarith

lemma Instance.exists_durationRoot (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {x : ℝ}
    (hx : optimalScalarValue P 1 0 < x) :
    ∃ d : ℝ, 0 < d ∧ d ≤ x ∧ optimalScalarValue P 1 d = x := by
  have hx0 : 0 < x := lt_of_le_of_lt (optimalScalarValue_nonnegative P hP zero_le_one le_rfl) hx
  have hcont : ContinuousOn (fun d ↦ optimalScalarValue P 1 d) (Icc (0 : ℝ) x) :=
    (optimalScalarValue_durationWeight_continuousOn P hP zero_le_one).mono (fun _ hd ↦ hd.1)
  have hupper := durationWeight_le_optimalScalarValue P hP (w := 1) zero_le_one hx0.le
  obtain ⟨d, hd, heq⟩ := intermediate_value_Icc hx0.le hcont ⟨hx.le, hupper⟩
  have hdne : d ≠ 0 := by
    intro hz
    rw [hz] at heq
    exact (ne_of_lt hx) heq
  exact ⟨d, lt_of_le_of_ne hd.1 hdne.symm, hd.2, heq⟩

/-- Below the reward-only value the root is set to zero; such levels have no
positive-horizon threshold crossing. Positive roots are constructed by IVT. -/
noncomputable def Instance.durationRoot (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (x : ℝ) : ℝ :=
  if hx : optimalScalarValue P 1 0 < x then Classical.choose (P.exists_durationRoot hP hx) else 0

lemma Instance.durationRoot_positive (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {x : ℝ}
    (hx : optimalScalarValue P 1 0 < x) : 0 < P.durationRoot hP x := by
  rw [Instance.durationRoot, dif_pos hx]
  exact (Classical.choose_spec (P.exists_durationRoot hP hx)).1

lemma Instance.durationRoot_eq_zero_of_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {x : ℝ}
    (hx : x ≤ optimalScalarValue P 1 0) : P.durationRoot hP x = 0 := by
  rw [Instance.durationRoot, dif_neg (not_lt.mpr hx)]

lemma Instance.durationRoot_nonnegative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (x : ℝ) : 0 ≤ P.durationRoot hP x := by
  by_cases hx : optimalScalarValue P 1 0 < x
  · exact (P.durationRoot_positive hP hx).le
  · rw [P.durationRoot_eq_zero_of_le hP (le_of_not_gt hx)]

lemma Instance.durationRoot_value (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {x : ℝ}
    (hx : optimalScalarValue P 1 0 < x) : optimalScalarValue P 1 (P.durationRoot hP x) = x := by
  rw [Instance.durationRoot, dif_pos hx]
  exact (Classical.choose_spec (P.exists_durationRoot hP hx)).2.2

lemma Instance.durationRoot_le_level (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {x : ℝ}
    (hx : optimalScalarValue P 1 0 < x) : P.durationRoot hP x ≤ x := by
  rw [Instance.durationRoot, dif_pos hx]
  exact (Classical.choose_spec (P.exists_durationRoot hP hx)).2.1

lemma Instance.durationRoot_value_ge (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (x : ℝ) : x ≤ optimalScalarValue P 1 (P.durationRoot hP x) := by
  by_cases hx : optimalScalarValue P 1 0 < x
  · rw [P.durationRoot_value hP hx]
  · rw [P.durationRoot_eq_zero_of_le hP (le_of_not_gt hx)]
    exact le_of_not_gt hx

lemma Instance.durationRoot_unique (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {x d : ℝ}
    (hx : optimalScalarValue P 1 0 < x) (hd : 0 ≤ d) (heq : optimalScalarValue P 1 d = x) :
    P.durationRoot hP x = d := by
  apply (P.rewardNormalized_strictMonoOn hP).injOn (P.durationRoot_nonnegative hP x) hd
  exact (P.durationRoot_value hP hx).trans heq.symm

lemma Instance.durationRoot_monotone (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) : Monotone (P.durationRoot hP) := by
  intro x y hxy
  by_cases hx : x ≤ optimalScalarValue P 1 0
  · rw [P.durationRoot_eq_zero_of_le hP hx]
    exact P.durationRoot_nonnegative hP y
  · have hx0 : optimalScalarValue P 1 0 < x := lt_of_not_ge hx
    have hy0 : optimalScalarValue P 1 0 < y := hx0.trans_le hxy
    by_contra hn
    have h := P.rewardNormalized_strictMonoOn hP (P.durationRoot_nonnegative hP y)
      (P.durationRoot_nonnegative hP x) (lt_of_not_ge hn)
    change optimalScalarValue P 1 (P.durationRoot hP y) < optimalScalarValue P 1 (P.durationRoot hP x) at h
    rw [P.durationRoot_value hP hy0, P.durationRoot_value hP hx0] at h
    exact not_lt_of_ge hxy h

lemma Instance.measurable_durationRoot (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) : Measurable (P.durationRoot hP) :=
  (P.durationRoot_monotone hP).measurable

lemma Instance.durationRoot_increment (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {x y : ℝ} (hxy : x ≤ y) :
    P.durationRoot hP y - P.durationRoot hP x ≤ 4 * (1 + (n : ℝ)) * (y - x) := by
  by_cases hy : y ≤ optimalScalarValue P 1 0
  · rw [P.durationRoot_eq_zero_of_le hP hy, P.durationRoot_eq_zero_of_le hP (hxy.trans hy), sub_self]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hxy)
  · have hy0 : optimalScalarValue P 1 0 < y := lt_of_not_ge hy
    have hg := P.remainingHorizon_growth hP (w := 1) (c := 1) zero_lt_one zero_le_one
      (P.durationRoot_nonnegative hP x) (P.durationRoot_monotone hP hxy)
    have hx0 := P.durationRoot_value_ge hP x
    rw [one_mul, one_mul, P.durationRoot_value hP hy0] at hg
    have hq : (P.durationRoot hP y - P.durationRoot hP x) / (4 * (1 + (n : ℝ))) ≤ y - x := by
      have he : (1 / (4 * (1 + (n : ℝ)))) * (P.durationRoot hP y - P.durationRoot hP x) =
          (P.durationRoot hP y - P.durationRoot hP x) / (4 * (1 + (n : ℝ))) := by ring
      rw [he] at hg
      linarith
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (1 + (n : ℝ)))).mp hq
    simpa only [mul_comm] using h

lemma Instance.durationRoot_lipschitz (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    LipschitzWith (NNReal.mk (4 * (1 + (n : ℝ))) (by positivity)) (P.durationRoot hP) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rcases le_total x y with hxy | hyx
  · have h := P.durationRoot_increment hP hxy
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (P.durationRoot_monotone hP hxy)),
      Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
    simpa only [neg_sub, NNReal.coe_mk] using h
  · have h := P.durationRoot_increment hP hyx
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (P.durationRoot_monotone hP hyx)),
      Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact h

lemma Instance.continuous_durationRoot (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) : Continuous (P.durationRoot hP) :=
  (P.durationRoot_lipschitz hP).continuous

noncomputable def Instance.crossingTime (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (z x : ℝ) : ℝ := 1 - P.durationRoot hP x / z

lemma Instance.crossingTime_mem_Ioo (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z x : ℝ} (hz : 0 < z)
    (hx : optimalScalarValue P 1 0 < x) (hroot : P.durationRoot hP x < z) :
    P.crossingTime hP z x ∈ Ioo (0 : ℝ) 1 := by
  have hp := div_pos (P.durationRoot_positive hP hx) hz
  have hlt := (div_lt_one hz).mpr hroot
  constructor <;> dsimp [Instance.crossingTime] <;> linarith

lemma Instance.value_at_crossingTime (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z x : ℝ} (hz : 0 < z)
    (hx : optimalScalarValue P 1 0 < x) :
    optimalScalarValue P 1 (z * (1 - P.crossingTime hP z x)) = x := by
  have ha : z * (1 - P.crossingTime hP z x) = P.durationRoot hP x := by
    unfold Instance.crossingTime
    rw [sub_sub_cancel, ← mul_div_assoc, mul_div_cancel_left₀ _ hz.ne']
  rw [ha, P.durationRoot_value hP hx]

lemma Instance.crossingTime_hasDerivAt (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 < z) (x : ℝ) :
    HasDerivAt (fun s ↦ P.crossingTime hP s x) (P.durationRoot hP x / z ^ 2) z := by
  have h := ((hasDerivAt_const z (P.durationRoot hP x)).fun_div (hasDerivAt_id z) hz.ne').const_sub 1
  simpa only [id_eq, zero_mul, mul_one, zero_sub, neg_div, neg_neg, Instance.crossingTime] using h

lemma Instance.crossingTime_normalized_formula (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
    P.crossingTime hP ((1 - lam) / lam) x = 1 - P.durationRoot hP x * lam / (1 - lam) := by
  unfold Instance.crossingTime
  field_simp [hlam.1.ne', (sub_pos.mpr hlam.2).ne']

lemma Instance.normalized_value_at_crossingTime (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam x : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (hx : optimalScalarValue P 1 0 < x) :
    optimalScalarValue P lam ((1 - lam) * (1 - P.crossingTime hP ((1 - lam) / lam) x)) = lam * x := by
  have harg : (1 - lam) * (1 - P.crossingTime hP ((1 - lam) / lam) x) = lam * P.durationRoot hP x := by
    rw [P.crossingTime_normalized_formula hP hlam x]
    field_simp [hlam.1.ne', (sub_pos.mpr hlam.2).ne']
    ring
  rw [harg]
  have h := optimalScalarValue_smul P hP (a := lam) (w := 1) (c := P.durationRoot hP x)
    hlam.1.le zero_le_one (P.durationRoot_nonnegative hP x)
  simpa only [mul_one, P.durationRoot_value hP hx] using h

end ProphetSecretary.Model
