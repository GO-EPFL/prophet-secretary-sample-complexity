import ProphetSecretary.Statistics.FixedPolicyEmpiricalUnbiased
import ProphetSecretary.Model.CompetitiveBasic

/-!
# The fixed-policy kernel for the normalized scalar gap

The policy and scalar are fixed before training. Clipped payoff observables
totalize the kernel, and on every valid offer vector it agrees with the paper's
kernel obtained by integrating arrival times and independent policy randomness.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

noncomputable def RandomizedPolicy.normalizedGameKernel (π : RandomizedPolicy n) (lam : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  lam*π.boundedScalarKernel ((1-lam)/lam) x -
    optimalCompetitiveRatio*(lam*Instance.maximum x+(1-lam))

lemma RandomizedPolicy.measurable_normalizedGameKernel (π : RandomizedPolicy n) (lam : ℝ) :
    Measurable (π.normalizedGameKernel lam) :=
  ((π.measurable_boundedScalarKernel ((1-lam)/lam)).const_mul lam).sub
    (((Instance.measurable_maximum.const_mul lam).add_const (1-lam)).const_mul optimalCompetitiveRatio)

private lemma boundedScalarKernel_nonnegative (π : RandomizedPolicy n) {z : ℝ} (hz : 0 ≤ z)
    (x : Fin n → ℝ) : 0 ≤ π.boundedScalarKernel z x := by
  apply integral_nonneg
  intro ur
  exact add_nonneg (boundedOfferValue_mem_range 1 _).1
    (mul_nonneg hz (boundedOfferValue_mem_range 1 _).1)

lemma RandomizedPolicy.normalizedGameKernel_abs_le_of_values_unit (π : RandomizedPolicy n)
    {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) : |π.normalizedGameKernel lam x| ≤ 1 := by
  let z := (1-lam)/lam
  have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr hlam.2) hlam.1.le
  have hlz : lam*z = 1-lam := by dsimp only [z]; field_simp [hlam.1.ne']
  have hk0 := boundedScalarKernel_nonnegative π hz x
  have hkB : π.boundedScalarKernel z x ≤ 1+z :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,abs_of_nonneg hz] using π.boundedScalarKernel_bound z x)
  have hJ0 : 0 ≤ lam*π.boundedScalarKernel z x := mul_nonneg hlam.1.le hk0
  have hJ1 : lam*π.boundedScalarKernel z x ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hkB hlam.1.le
    nlinarith only [h,hlz]
  have hm0 := Instance.maximum_nonnegative x
  have hm1 := Instance.maximum_le x zero_le_one (fun i => (hx i).2)
  have hB0 : 0 ≤ lam*Instance.maximum x+(1-lam) :=
    add_nonneg (mul_nonneg hlam.1.le hm0) (sub_nonneg.mpr hlam.2)
  have hB1 : lam*Instance.maximum x+(1-lam) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hm1 hlam.1.le
    linarith only [h]
  have hC0 := mul_nonneg optimalCompetitiveRatio_nonnegative hB0
  have hC1 : optimalCompetitiveRatio*(lam*Instance.maximum x+(1-lam)) ≤ 1 :=
    (mul_le_mul_of_nonneg_right optimalCompetitiveRatio_le_one hB0).trans (by simpa only [one_mul] using hB1)
  exact abs_le.mpr ⟨by change -1 ≤ lam*π.boundedScalarKernel z x-_; linarith only [hJ0,hC1],
    by change lam*π.boundedScalarKernel z x-_ ≤ 1; linarith only [hJ1,hC0]⟩

lemma RandomizedPolicy.normalizedGameKernel_abs_le_ae (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) :
    ∀ᵐ x ∂P.valuesLaw, |π.normalizedGameKernel lam x| ≤ 1 := by
  have hu := (ae_all_iff.mpr (fun i => (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hcap i)))
  filter_upwards [P.ae_nonnegative,hu] with x hx hu
  exact π.normalizedGameKernel_abs_le_of_values_unit hlam x (fun i => ⟨hx i,hu i⟩)

lemma RandomizedPolicy.boundedScalarKernel_eq_unclipped (π : RandomizedPolicy n)
    (z : ℝ) (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    π.boundedScalarKernel z x = ∫ ur,
      (π.realizedReward (x,ur)+z*π.realizedDuration (x,ur)) ∂(Instance.clocksLaw n).prod π.seedLaw := by
  have hClock : ∀ᵐ ur ∂(Instance.clocksLaw n).prod π.seedLaw, ∀ i, ur.1 i ∈ Icc (0 : ℝ) 1 :=
    (measurePreserving_fst (μ := Instance.clocksLaw n) (ν := π.seedLaw)).quasiMeasurePreserving.ae
      (Instance.clocks_mem_unitInterval (n := n))
  apply integral_congr_ae
  filter_upwards [hClock] with ur hu
  exact congrArg₂ (fun r d => r+z*d)
    (π.rule.boundedRewardObservable_eq 1 ur.2 Finset.univ x ur.1 hx)
    (π.rule.boundedDurationObservable_eq ur.2 Finset.univ x ur.1 (fun i => (hu i).1))

/-- Equality with the manuscript's kernel at every valid offer vector, after
averaging physical clocks and independent policy randomness. -/
lemma RandomizedPolicy.normalizedGameKernel_eq_unclipped (π : RandomizedPolicy n)
    {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    π.normalizedGameKernel lam x =
      (∫ ur, (lam*π.realizedReward (x,ur)+(1-lam)*π.realizedDuration (x,ur))
        ∂(Instance.clocksLaw n).prod π.seedLaw) -
      optimalCompetitiveRatio*(lam*Instance.maximum x+(1-lam)) := by
  let z := (1-lam)/lam
  have hlz : lam*z = 1-lam := by dsimp only [z]; field_simp [hlam.1.ne']
  have hInt : lam*π.boundedScalarKernel z x =
      ∫ ur, (lam*π.realizedReward (x,ur)+(1-lam)*π.realizedDuration (x,ur))
        ∂(Instance.clocksLaw n).prod π.seedLaw := by
    rw [π.boundedScalarKernel_eq_unclipped z x hx,← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ur => by dsimp only; rw [mul_add,← mul_assoc,hlz])
  change lam*π.boundedScalarKernel z x-_ = _
  rw [hInt]

lemma RandomizedPolicy.integral_normalizedGameKernel (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {lam : ℝ} (hlam : lam ∈ Ioc (0 : ℝ) 1) :
    (∫ x, π.normalizedGameKernel lam x ∂P.valuesLaw) = π.scalarObjective P lam (1-lam) -
      optimalCompetitiveRatio*(lam*P.expectedMaximum+(1-lam)) := by
  let z := (1-lam)/lam
  have hlz : lam*z = 1-lam := by dsimp only [z]; field_simp [hlam.1.ne']
  have hP := P.integrable_maximum_of_bounded hcap
  have hK : Integrable (π.boundedScalarKernel z) P.valuesLaw :=
    Integrable.of_bound (π.measurable_boundedScalarKernel z).aestronglyMeasurable (1+|z|)
      (Filter.Eventually.of_forall (π.boundedScalarKernel_bound z))
  have hB : Integrable (fun x => optimalCompetitiveRatio*(lam*Instance.maximum x+(1-lam))) P.valuesLaw :=
    ((hP.const_mul lam).add (integrable_const (1-lam))).const_mul optimalCompetitiveRatio
  have hJB : lam*π.scalarObjective P 1 z = π.scalarObjective P lam (1-lam) := by
    rw [π.scalarObjective_eq P hP 1 z,π.scalarObjective_eq P hP lam (1-lam)]
    simp only [one_mul]
    rw [mul_add,← mul_assoc,hlz]
  change (∫ x, lam*π.boundedScalarKernel z x -
    optimalCompetitiveRatio*(lam*Instance.maximum x+(1-lam)) ∂P.valuesLaw) = _
  rw [integral_sub (hK.const_mul lam) hB,integral_const_mul,
    ← π.scalarObjective_eq_boundedScalarKernel P hcap z,
    integral_const_mul,integral_add (hP.const_mul lam) (integrable_const (1-lam)),integral_const_mul]
  simp only [integral_const,probReal_univ,one_smul]
  rw [hJB]
  rfl

end ProphetSecretary.Model
