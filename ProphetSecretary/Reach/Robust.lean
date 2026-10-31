import ProphetSecretary.Reach.RobustFinite
import ProphetSecretary.Reach.ErrorLimits
import ProphetSecretary.Reach.RareReach
import ProphetSecretary.Model.BoundedBenchmark

/-!
# The global reward--duration inequality

Paper correspondence: `lem:robust` = `upmom:global`. The finite multi-jackpot estimates
are uniform over all policies. Their jackpot probability first tends to zero at a fixed
number of dummies; only then does the number of zero identities tend to infinity.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- Unit reward weight. The dummy-count error remains explicit until the final limit. -/
lemma globalScalar_unitReward (P : Instance n) {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H) :
    optimalCompetitiveRatio * (P.expectedMaximum + D) ≤ optimalScalarValue P 1 D := by
  apply ProphetSecretary.Reach.le_of_forall_nat_sqrt_error (K := 20 * D)
  intro N hN
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  apply reach_of_arbitrarily_small_jackpot_error
    (K := 2 * (H + D) * (N : ℝ)) (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hH hD)) hNr.le)
  intro p hp hp1
  let pp : unitInterval := ⟨p, hp.le, hp1⟩
  let A : ℝ := D / ((N : ℝ) * p)
  have hA : 0 ≤ A := div_nonneg hD (mul_nonneg hNr.le hp.le)
  let Q := P.appendJackpots N pp A hA
  let E : ℝ := (H + D) * N * p
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg (add_nonneg hH hD) hNr.le) hp.le
  have hDfix : A * N * (pp : ℝ) = D := by
    dsimp [A, pp]
    field_simp
  have hError : H * N * (pp : ℝ) + A * (N : ℝ) ^ 2 * (pp : ℝ) ^ 2 = E := by
    dsimp [A, pp, E]
    field_simp
  have hlower0 := MultiJackpot.appendJackpots_expectedMaximum_lower P N pp hH hA hbound
  have hlower : P.expectedMaximum + D - E ≤ Q.expectedMaximum := by
    rw [hDfix] at hlower0
    linarith [hError]
  have hQ : Integrable Instance.maximum Q.valuesLaw :=
    P.appendJackpots_integrable_maximum N pp hA hH hbound
  have hglobal := optimalReward_ge_globalRatio_of_integrable Q hQ
  have hupper0 := MultiJackpot.appendJackpots_optimalReward_le_scalar P N hN pp hH hA hbound
  have hupper : optimalScalarValue Q 1 0 ≤ optimalScalarValue P 1 D + 20 * D / Real.sqrt (N : ℝ) + E := by
    rw [hDfix] at hupper0
    linarith [hError]
  have hprod := mul_le_mul_of_nonneg_left hlower optimalCompetitiveRatio_nonnegative
  have hCerror := mul_le_mul_of_nonneg_right optimalCompetitiveRatio_le_one hE
  have hchain := hprod.trans (hglobal.trans hupper)
  change optimalCompetitiveRatio * (P.expectedMaximum + D) ≤
    optimalScalarValue P 1 D + 20 * D / Real.sqrt (N : ℝ) + (2 * (H + D) * N) * p
  dsimp [E] at hchain hCerror
  nlinarith

/-- The finite bounded global scalar comparison, over the full admissible policy class. -/
theorem globalScalar_inequality (P : Instance n) {H w c : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ j, ∀ᵐ x ∂P.law j, x ≤ H)
    (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalCompetitiveRatio * (w * P.expectedMaximum + c) ≤ optimalScalarValue P w c := by
  have hP := P.integrable_maximum_of_bounded hbound
  by_cases hw0 : w = 0
  · subst w
    have hC := mul_le_mul_of_nonneg_right optimalCompetitiveRatio_le_one hc
    have hCc : optimalCompetitiveRatio * c ≤ c := by simpa only [one_mul] using hC
    simpa only [zero_mul, zero_add] using
      hCc.trans (durationWeight_le_optimalScalarValue P hP (w := 0) (c := c) le_rfl hc)
  have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hD : 0 ≤ c / w := div_nonneg hc hw
  have hbase := globalScalar_unitReward P hH hD hbound
  have hm := mul_le_mul_of_nonneg_left hbase hw
  have hscale := optimalScalarValue_smul P hP hw zero_le_one hD
  have hwD : w * (c / w) = c := mul_div_cancel₀ c hwpos.ne'
  rw [mul_one, hwD] at hscale
  rw [← hscale] at hm
  have he : w * (optimalCompetitiveRatio * (P.expectedMaximum + c / w)) =
      optimalCompetitiveRatio * (w * P.expectedMaximum + c) := by
    field_simp
  rw [he] at hm
  exact hm

/-- Capping transfers the bounded inequality to every finite integrable instance.
The limits keep the original instance size fixed and use actual policy transports. -/
theorem globalScalar_inequality_of_integrable (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalCompetitiveRatio * (w * P.expectedMaximum + c) ≤ optimalScalarValue P w c := by
  have hM := P.cap_expectedMaximum_tendsto hP
  have hV := optimalScalarValue_cap_tendsto P hP hw hc
  have hL : Tendsto (fun H : ℝ≥0 => optimalCompetitiveRatio *
      (w * (P.cap H).expectedMaximum + c)) atTop
      (𝓝 (optimalCompetitiveRatio * (w * P.expectedMaximum + c))) :=
    ((hM.const_mul w).add_const c).const_mul optimalCompetitiveRatio
  apply le_of_tendsto_of_tendsto hL hV
  exact Filter.Eventually.of_forall fun H =>
    globalScalar_inequality (P.cap H) H.coe_nonneg (P.cap_bounded H) hw hc

lemma scalarGap_nonnegative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    0 ≤ scalarGap P w c :=
  sub_nonneg.mpr (globalScalar_inequality_of_integrable P hP hw hc)

lemma normalizedScalarGap_nonnegative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) 1) :
    0 ≤ normalizedScalarGap P lam :=
  scalarGap_nonnegative P hP hlam.1 (sub_nonneg.mpr hlam.2)

/-- All bounded scalar benchmarks, allowing zero-mean offers when duration is rewarded. -/
def boundedScalarRatios : Set ℝ :=
  {r | ∃ (n : ℕ) (P : Instance n) (H : ℝ≥0) (w c : ℝ),
    (∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) ∧ 0 ≤ w ∧ 0 ≤ c ∧
      0 < w * P.expectedMaximum + c ∧ r = optimalScalarValue P w c / (w * P.expectedMaximum + c)}

noncomputable def boundedScalarRatio : ℝ := sInf boundedScalarRatios

lemma boundedScalarRatios_nonempty : boundedScalarRatios.Nonempty := by
  refine ⟨_, 1, unitOfferInstance, 1, 1, 0, ?_, zero_le_one, le_rfl, ?_, rfl⟩
  · intro i
    simp [unitOfferInstance]
  · simp [unitOfferInstance_expectedMaximum]

lemma boundedScalarRatios_ge_global {r : ℝ} (hr : r ∈ boundedScalarRatios) :
    optimalCompetitiveRatio ≤ r := by
  obtain ⟨n, P, H, w, c, hbound, hw, hc, hden, rfl⟩ := hr
  exact (le_div_iff₀ hden).mpr (globalScalar_inequality P H.coe_nonneg hbound hw hc)

lemma boundedScalarRatios_bddBelow : BddBelow boundedScalarRatios :=
  ⟨optimalCompetitiveRatio, fun _ hr => boundedScalarRatios_ge_global hr⟩

/-- The sharpness statement in `lem:robust`. Bounded-instance sufficiency is proved
using actual truncated-policy approximations, rather than assumed from value convergence. -/
theorem boundedScalarRatio_eq_optimalCompetitiveRatio : boundedScalarRatio = optimalCompetitiveRatio := by
  apply le_antisymm
  · rw [← boundedCompetitiveRatio_eq_optimalCompetitiveRatio]
    apply le_csInf boundedCompetitiveRatios_nonempty
    rintro r ⟨n, P, H, hP, hbound, rfl⟩
    have hden : 0 < 1 * P.expectedMaximum + 0 := by simpa only [one_mul, add_zero] using hP.2
    have hmem : optimalScalarValue P 1 0 / (1 * P.expectedMaximum + 0) ∈ boundedScalarRatios :=
      ⟨n, P, H, 1, 0, hbound, zero_le_one, le_rfl, hden, rfl⟩
    simpa only [boundedScalarRatio, one_mul, add_zero] using csInf_le boundedScalarRatios_bddBelow hmem
  · exact le_csInf boundedScalarRatios_nonempty (fun _ hr => boundedScalarRatios_ge_global hr)

end ProphetSecretary.Model

