import ProphetSecretary.Statistics.PlannerRoundedCoupling
import ProphetSecretary.Statistics.ScalarPlannerRecursion

/-!
# The rounded planner's operator error

The same seed produces the ideal and grid executions. On matching recorded
discrete data, only the fraction changes; on the exceptional event the
integrand lies in an interval of length one.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Analysis

theorem plannerRoundedExpectation_error {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (N : ℕ) (hN : 0 < N) (f : PlannerUniformOutput n → ℝ) (hf : Measurable f)
    (hb : ∀ o, o.2.1 ∈ Icc (0 : ℝ) 1 → 0 ≤ f o ∧ f o ≤ 1)
    (hlip : ∀ (i : Option (Fin n)) (B : Finset (Fin n)) (s t : ℝ),
      s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |f (i,s,B) - f (i,t,B)| ≤ 4*|s-t|) :
    |(∫ seed, f (plannerUniformTransition A p seed) ∂plannerUniformSeedLaw n) -
      (∫ seed, f (plannerRoundedTransition A p N hN seed) ∂plannerUniformSeedLaw n)| ≤
      (10 * (n : ℝ) + 4) / N := by
  let μ := plannerUniformSeedLaw n
  let L := fun seed => f (plannerUniformTransition A p seed)
  let R := fun seed => f (plannerRoundedTransition A p N hN seed)
  let E : Set (PlannerUniformSeed n) := {seed | plannerAugmentedDiscreteOutput A p seed ≠
    plannerAugmentedDiscreteOutput A p (plannerRoundSeed N hN seed)}
  have hE : MeasurableSet E := (measurableSet_eq_fun (plannerAugmentedDiscreteOutput_measurable A p)
    ((plannerAugmentedDiscreteOutput_measurable A p).comp (measurable_plannerRoundSeed n N hN))).compl
  have hInt (g : PlannerUniformSeed n → ℝ) (hg : Measurable g)
      (hbg : ∀ seed, 0 ≤ g seed ∧ g seed ≤ 1) : Integrable g μ := by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    exact ae_of_all _ (fun seed => by rw [Real.norm_eq_abs, abs_of_nonneg (hbg seed).1]; exact (hbg seed).2)
  have hL : Integrable L μ := hInt L (hf.comp (measurable_plannerUniformTransition A p))
    (fun seed => hb _ (plannerUniformTransition_fraction_mem_unit A p seed))
  have hR : Integrable R μ := hInt R (hf.comp (measurable_plannerRoundedTransition A p N hN))
    (fun seed => hb _ (plannerUniformTransition_fraction_mem_unit A p (plannerRoundSeed N hN seed)))
  have hpoint : ∀ᵐ seed ∂μ, |L seed - R seed| ≤ E.indicator 1 seed + 4 * (1 / (N : ℝ)) := by
    filter_upwards [plannerRoundedTransition_fraction_error_on_matching_subset A p N hN] with seed hs
    let a := plannerUniformTransition A p seed
    let b := plannerRoundedTransition A p N hN seed
    have ha : a.2.1 ∈ Icc (0 : ℝ) 1 := plannerUniformTransition_fraction_mem_unit A p seed
    have hb' : b.2.1 ∈ Icc (0 : ℝ) 1 :=
      plannerUniformTransition_fraction_mem_unit A p (plannerRoundSeed N hN seed)
    change |f a - f b| ≤ _
    by_cases he : seed ∈ E
    · have hd : |f a - f b| ≤ 1 := abs_le.mpr
        ⟨by linarith [(hb a ha).1, (hb b hb').2], by linarith [(hb a ha).2, (hb b hb').1]⟩
      simp only [Set.indicator_of_mem he, Pi.one_apply]
      exact hd.trans (le_add_of_nonneg_right (by positivity))
    · have heq : plannerAugmentedDiscreteOutput A p seed =
          plannerAugmentedDiscreteOutput A p (plannerRoundSeed N hN seed) := not_ne_iff.mp he
      have hD : plannerRecordedSubset A p seed.1 =
          plannerRecordedSubset A p (plannerRoundSeed N hN seed).1 := congrArg Prod.fst heq
      have hdisc : plannerDiscreteOutput a = plannerDiscreteOutput b := congrArg Prod.snd heq
      have hI : a.1 = b.1 := congrArg (fun q : Option (Fin n) × Finset (Fin n) => q.1) hdisc
      have hB : a.2.2 = b.2.2 := congrArg (fun q : Option (Fin n) × Finset (Fin n) => q.2) hdisc
      have hfrac : |a.2.1-b.2.1| ≤ 1/(N:ℝ) := hs hD
      simp only [Set.indicator_of_notMem he, zero_add]
      calc
        _ = |f (a.1,a.2.1,a.2.2) - f (a.1,b.2.1,a.2.2)| := by
          change |f (a.1,a.2.1,a.2.2) - f (b.1,b.2.1,b.2.2)| = _
          rw [← hI, ← hB]
        _ ≤ 4 * |a.2.1-b.2.1| := hlip _ _ _ _ ha hb'
        _ ≤ _ := mul_le_mul_of_nonneg_left hfrac (by norm_num)
  have hiE : Integrable (E.indicator (1 : PlannerUniformSeed n → ℝ)) μ :=
    (integrable_const 1).indicator hE
  have hiR : Integrable (fun seed => E.indicator 1 seed + 4*(1/(N:ℝ))) μ :=
    hiE.add (integrable_const _)
  have hiL : Integrable (fun seed => |L seed-R seed|) μ := (hL.sub hR).abs
  change |(∫ seed, L seed ∂μ) - (∫ seed, R seed ∂μ)| ≤ _
  calc
    _ = |∫ seed, L seed - R seed ∂μ| := by rw [integral_sub hL hR]
    _ ≤ ∫ seed, |L seed - R seed| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ seed, E.indicator 1 seed + 4*(1/(N:ℝ)) ∂μ := integral_mono_ae hiL hiR hpoint
    _ = μ.real E + 4*(1/(N:ℝ)) := by
      rw [integral_add hiE (integrable_const _), integral_indicator_one hE]
      simp
    _ ≤ 10*(n:ℝ)/N + 4*(1/(N:ℝ)) := add_le_add (plannerAugmentedDiscreteOutput_rounded_probability A p N hN) le_rfl
    _ = _ := by ring

variable {n : ℕ} {k : Fin n → ℕ} [∀ i, NeZero (k i)]

lemma scalarPlannerReferenceIntegrand_bounds (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1) (x : ScalarPlannerState n)
    (o : PlannerUniformOutput n) :
    0 ≤ scalarPlannerReferenceIntegrand y hy x o ∧ scalarPlannerReferenceIntegrand y hy x o ≤ 1 := by
  cases ho : o.1 with
  | none => simp [scalarPlannerReferenceIntegrand, ho]
  | some i =>
    simp only [scalarPlannerReferenceIntegrand, ho]
    have hb := weightedContinuationIntegrand_abs_le_one y hy hcap (plannerUnit_mem x.2.1).1
      (scalarPlannerDurationWeight_mem x).1 (i,o.2)
    exact ⟨div_nonneg (empiricalConditionalExcess_nonnegative _ _)
      (scalarPlannerWeight_pos y o.2.2).le, (le_abs_self _).trans hb⟩

lemma scalarPlannerReferenceIntegrand_fraction_lipschitz (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (x : ScalarPlannerState n) (i : Option (Fin n))
    (B : Finset (Fin n)) (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |scalarPlannerReferenceIntegrand y hy x (i,s,B) -
      scalarPlannerReferenceIntegrand y hy x (i,t,B)| ≤ 4*|s-t| := by
  cases i with
  | none => simp [scalarPlannerReferenceIntegrand]
  | some i =>
    let Q := empiricalPlannerInstance y hy
    let A := plannerActive y B
    let u := scalarPlannerTime x
    let z := scalarPlannerDurationWeight x
    let β := scalarPlannerWeight y B
    let a := Q.continuationValue A (u*s) 1 z
    let b := Q.continuationValue A (u*t) 1 z
    have hu : u ∈ Icc (0 : ℝ) 1 := plannerUnit_mem _
    have hz : z ∈ Icc (0 : ℝ) 4 := scalarPlannerDurationWeight_mem x
    have hβ : 0 < β := scalarPlannerWeight_pos y B
    have hQ := empiricalPlannerInstance_integrable y hy
    have hL : |a-b| ≤ |z*(u*s)-z*(u*t)| := by
      have hv := optimalScalarValue_coefficients_lipschitz (Q.restrictTo A)
        (Q.restrictTo_integrable_maximum A hQ) zero_le_one
        (mul_nonneg hz.1 (mul_nonneg hu.1 hs.1)) zero_le_one (mul_nonneg hz.1 (mul_nonneg hu.1 ht.1))
      simpa only [a, b, Instance.continuationValue, sub_self, abs_zero, mul_zero, zero_add] using hv
    have hzu : z*u ≤ 4 := (mul_le_of_le_one_right hz.1 hu.2).trans hz.2
    simp only [scalarPlannerReferenceIntegrand, weightedContinuationIntegrand, plannerUnit_eq hs, plannerUnit_eq ht]
    change |empiricalConditionalExcess (y i) a/β - empiricalConditionalExcess (y i) b/β| ≤ _
    rw [← sub_div, abs_div, abs_of_pos hβ]
    apply (div_le_iff₀ hβ).2
    calc
      _ ≤ |a-b| := empiricalConditionalExcess_lipschitz (y i) a b
      _ ≤ |z*(u*s)-z*(u*t)| := hL
      _ = (z*u)*|s-t| := by
        rw [show z*(u*s)-z*(u*t)=(z*u)*(s-t) by ring, abs_mul,
          abs_of_nonneg (mul_nonneg hz.1 hu.1)]
      _ ≤ 4*|s-t| := mul_le_mul_of_nonneg_right hzu (abs_nonneg _)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (scalarPlannerWeight_ge_one y B)

noncomputable def scalarPlannerRoundedRecursion (y : (i : Fin n) → Fin (k i) → ℝ)
    (N : ℕ) (hN : 0 < N) :
    MultilevelRecursion (ScalarPlannerState n) (PlannerUniformSeed n) (PlannerUniformOutput n) ℝ :=
  { scalarPlannerRecursion y with
    sample := fun x seed => (scalarPlannerRecursion y).sample x (plannerRoundSeed N hN seed) }

omit [∀ i, NeZero (k i)] in
lemma scalarPlannerRoundedRecursion_measurable (y : (i : Fin n) → Fin (k i) → ℝ)
    (N : ℕ) (hN : 0 < N) : (scalarPlannerRoundedRecursion y N hN).IsMeasurable := by
  have hd := scalarPlannerRecursion_measurable y
  exact ⟨hd.isEmpty, hd.emptyValue, hd.offset, hd.coefficient,
    hd.sample.comp (measurable_fst.prodMk ((measurable_plannerRoundSeed n N hN).comp measurable_snd)),
    hd.child, hd.payoff⟩

/-- First inequality in `bits:operator-error`, evaluated at the actual true
normalized continuation. -/
theorem scalarPlannerNormalizedValue_rounded_residual (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1) (x : ScalarPlannerState n)
    (hx : (scalarPlannerRecursion y).isEmpty x = false) (N : ℕ) (hN : 0 < N) :
    let D := scalarPlannerRoundedRecursion y N hN
    let v := scalarPlannerNormalizedValue y hy
    |v x - (D.offset x + D.coefficient x * ∫ seed,
      D.payoff x (D.sample x seed) (v (D.child x (D.sample x seed))) ∂plannerUniformSeedLaw n)| ≤
      (10 * (n : ℝ) + 4) / (4 * (N : ℝ)) := by
  let A := plannerActive y x.1
  let p := plannerPositiveProbability y
  let F := scalarPlannerReferenceIntegrand y hy x
  let μ := plannerUniformSeedLaw n
  let D := scalarPlannerRecursion y
  let R := scalarPlannerRoundedRecursion y N hN
  let v := scalarPlannerNormalizedValue y hy
  let L := ∫ seed, F (plannerUniformTransition A p seed) ∂μ
  let B := ∫ seed, F (plannerRoundedTransition A p N hN seed) ∂μ
  have hL : (∫ seed, D.payoff x (D.sample x seed) (v (D.child x (D.sample x seed))) ∂μ) = L := by
    apply integral_congr_ae
    exact ae_of_all _ (fun seed => scalarPlannerPayoff_at_normalizedChild y hy x (D.sample x seed))
  have hB : (∫ seed, R.payoff x (R.sample x seed) (v (R.child x (R.sample x seed))) ∂μ) = B := by
    apply integral_congr_ae
    exact ae_of_all _ (fun seed => scalarPlannerPayoff_at_normalizedChild y hy x (R.sample x seed))
  have hfix := scalarPlannerNormalizedValue_fixed y hy hcap x hx
  change v x = D.offset x + D.coefficient x *
    (∫ seed, D.payoff x (D.sample x seed) (v (D.child x (D.sample x seed))) ∂μ) at hfix
  rw [hL] at hfix
  have he : |L-B| ≤ (10*(n:ℝ)+4)/N := plannerRoundedExpectation_error A p N hN F
    (measurable_scalarPlannerReferenceIntegrand y hy x)
    (fun o _ => scalarPlannerReferenceIntegrand_bounds y hy hcap x o)
    (scalarPlannerReferenceIntegrand_fraction_lipschitz y hy x)
  have hc := scalarPlannerRecursion_coefficient_bounds y x
  change |v x - (D.offset x + D.coefficient x *
    (∫ seed, R.payoff x (R.sample x seed) (v (R.child x (R.sample x seed))) ∂μ))| ≤ _
  rw [hB, hfix, show D.offset x + D.coefficient x * L - (D.offset x + D.coefficient x * B) =
    D.coefficient x * (L-B) by ring, abs_mul, abs_of_nonneg hc.1]
  calc
    _ ≤ D.coefficient x * ((10*(n:ℝ)+4)/N) := mul_le_mul_of_nonneg_left he hc.1
    _ ≤ (1/4 : ℝ) * ((10*(n:ℝ)+4)/N) := mul_le_mul_of_nonneg_right hc.2 (by positivity)
    _ = _ := by ring

end ProphetSecretary.Statistics
