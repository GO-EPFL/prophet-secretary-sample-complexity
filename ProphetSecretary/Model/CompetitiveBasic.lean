import ProphetSecretary.Model.ScalarValueProperties

/-!
# The global competitive ratio and an individual instance

`optimalCompetitiveRatio` is an infimum over all positive finite benchmarks.
These elementary bounds use an explicit one-offer witness and do not invoke
an external numerical prophet-secretary bound.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

/-- A single deterministic offer of value one. -/
noncomputable def unitOfferInstance : Instance 1 where
  law := fun _ ↦ Measure.dirac (1 : ℝ)
  probability := fun _ ↦ inferInstance
  nonnegative := fun _ ↦ by simp

theorem unitOfferInstance_values :
    ∀ᵐ x ∂unitOfferInstance.valuesLaw, ∀ i, x i = 1 := by
  rw [ae_all_iff]
  intro i
  have hi : ∀ᵐ x ∂unitOfferInstance.law i, x = (1 : ℝ) := by simp [unitOfferInstance]
  exact (measurePreserving_eval unitOfferInstance.law i).quasiMeasurePreserving.ae hi

theorem unitOfferInstance_integrable_maximum :
    Integrable Instance.maximum unitOfferInstance.valuesLaw := by
  apply unitOfferInstance.integrable_maximum_of_bounded (H := 1)
  intro i
  simp [unitOfferInstance]

theorem unitOfferInstance_expectedMaximum : unitOfferInstance.expectedMaximum = 1 := by
  have heq : Instance.maximum =ᵐ[unitOfferInstance.valuesLaw] fun _ ↦ (1 : ℝ) := by
    filter_upwards [unitOfferInstance_values] with x hx
    apply le_antisymm
    · exact Instance.maximum_le x zero_le_one (fun i ↦ (hx i).le)
    · have h := Instance.le_maximum x (0 : Fin 1)
      simpa only [hx 0] using h
  unfold Instance.expectedMaximum
  rw [integral_congr_ae heq]
  simp

theorem unitOfferInstance_positiveFinite : unitOfferInstance.HasPositiveFiniteMaximum :=
  ⟨unitOfferInstance_integrable_maximum, by rw [unitOfferInstance_expectedMaximum]; norm_num⟩

/-- Every individual-instance optimal reward ratio belongs to `[0,1]`. -/
theorem instanceCompetitiveRatio_mem_unitInterval {n : ℕ} (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) :
    optimalScalarValue P 1 0 / P.expectedMaximum ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (optimalScalarValue_nonnegative P hP.1 zero_le_one le_rfl) hP.2.le
  · apply (div_le_one hP.2).mpr
    simpa only [one_mul, add_zero] using
      optimalScalarValue_le_benchmark P hP.1 (w := 1) (c := 0) zero_le_one le_rfl

theorem competitiveRatios_nonempty :
    {r | ∃ (n : ℕ) (P : Instance n), P.HasPositiveFiniteMaximum ∧
      r = optimalScalarValue P 1 0 / P.expectedMaximum}.Nonempty :=
  ⟨_, 1, unitOfferInstance, unitOfferInstance_positiveFinite, rfl⟩

theorem competitiveRatios_bddBelow :
    BddBelow {r | ∃ (n : ℕ) (P : Instance n), P.HasPositiveFiniteMaximum ∧
      r = optimalScalarValue P 1 0 / P.expectedMaximum} := by
  refine ⟨0, ?_⟩
  rintro r ⟨n, P, hP, rfl⟩
  exact (instanceCompetitiveRatio_mem_unitInterval P hP).1

/-- The global guarantee is at most the optimal reward ratio of every instance.
This is not an assertion that an individual instance attains the global infimum. -/
theorem optimalCompetitiveRatio_le_instance {n : ℕ} (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) :
    optimalCompetitiveRatio ≤ optimalScalarValue P 1 0 / P.expectedMaximum :=
  csInf_le competitiveRatios_bddBelow ⟨n, P, hP, rfl⟩

theorem optimalCompetitiveRatio_nonnegative : 0 ≤ optimalCompetitiveRatio := by
  apply le_csInf competitiveRatios_nonempty
  rintro r ⟨n, P, hP, rfl⟩
  exact (instanceCompetitiveRatio_mem_unitInterval P hP).1

theorem optimalCompetitiveRatio_le_one : optimalCompetitiveRatio ≤ 1 :=
  (optimalCompetitiveRatio_le_instance unitOfferInstance unitOfferInstance_positiveFinite).trans
    (instanceCompetitiveRatio_mem_unitInterval unitOfferInstance unitOfferInstance_positiveFinite).2

/-- The reward-only competitive inequality follows from the definition of the
global constant. The duration-weighted extension is `lem:robust` and needs a
separate proof. -/
theorem optimalReward_ge_globalRatio {n : ℕ} (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) :
    optimalCompetitiveRatio * P.expectedMaximum ≤ optimalScalarValue P 1 0 :=
  (le_div_iff₀ hP.2).mp (optimalCompetitiveRatio_le_instance P hP)

/-- The reward-only comparison also permits bounded zero-mean auxiliary
instances. Positivity is needed only to form an individual competitive ratio. -/
theorem optimalReward_ge_globalRatio_of_integrable {n : ℕ} (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    optimalCompetitiveRatio * P.expectedMaximum ≤ optimalScalarValue P 1 0 := by
  by_cases hM : 0 < P.expectedMaximum
  · exact optimalReward_ge_globalRatio P ⟨hP, hM⟩
  have hz : P.expectedMaximum = 0 := le_antisymm (le_of_not_gt hM) P.expectedMaximum_nonnegative
  rw [hz, mul_zero]
  exact optimalScalarValue_nonnegative P hP zero_le_one le_rfl

/-- The scalar gap remains convex after subtracting the affine competitive
benchmark. This is the convexity used for critical scalar sublevels. -/
theorem normalizedScalarGap_convex {n : ℕ} (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (normalizedScalarGap P) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := (optimalScalarValue_weight_convex P hP).2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have hb' : b = 1 - a := by linarith
  rw [hb'] at h ⊢
  unfold normalizedScalarGap scalarGap
  nlinarith

/-- The normalized scalar gap has the paper's dimension-free Lipschitz bound,
using only the elementary `0≤C_PS≤1` rather than an external numerical theorem. -/
theorem normalizedScalarGap_weight_lipschitz {n : ℕ} (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam rho : ℝ}
    (hlam : lam ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 1) :
    |normalizedScalarGap P lam - normalizedScalarGap P rho| ≤
      2 * (P.expectedMaximum + 1) * |lam - rho| := by
  have hC0 := optimalCompetitiveRatio_nonnegative
  have hC1 := optimalCompetitiveRatio_le_one
  have hM0 := P.expectedMaximum_nonnegative
  have hM1 : |P.expectedMaximum - 1| ≤ P.expectedMaximum + 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hbase : |optimalCompetitiveRatio * (lam * P.expectedMaximum + (1 - lam)) -
      optimalCompetitiveRatio * (rho * P.expectedMaximum + (1 - rho))| ≤
      (P.expectedMaximum + 1) * |lam - rho| := by
    have heq : optimalCompetitiveRatio * (lam * P.expectedMaximum + (1 - lam)) -
        optimalCompetitiveRatio * (rho * P.expectedMaximum + (1 - rho)) =
        optimalCompetitiveRatio * (lam - rho) * (P.expectedMaximum - 1) := by ring
    rw [heq, abs_mul, abs_mul, abs_of_nonneg hC0]
    calc
      _ ≤ (1 * |lam - rho|) * (P.expectedMaximum + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hC1 (abs_nonneg _)) hM1
          (abs_nonneg _) (by positivity)
      _ = _ := by ring

  calc
    |normalizedScalarGap P lam - normalizedScalarGap P rho| =
        |(optimalScalarValue P lam (1 - lam) - optimalScalarValue P rho (1 - rho)) -
          (optimalCompetitiveRatio * (lam * P.expectedMaximum + (1 - lam)) -
            optimalCompetitiveRatio * (rho * P.expectedMaximum + (1 - rho)))| := by
      congr 1
      unfold normalizedScalarGap scalarGap
      ring
    _ ≤ |optimalScalarValue P lam (1 - lam) - optimalScalarValue P rho (1 - rho)| +
        |optimalCompetitiveRatio * (lam * P.expectedMaximum + (1 - lam)) -
          optimalCompetitiveRatio * (rho * P.expectedMaximum + (1 - rho))| := by simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le _ (0 : ℝ) _)
    _ ≤ (P.expectedMaximum + 1) * |lam - rho| +
        (P.expectedMaximum + 1) * |lam - rho| :=
      add_le_add (optimalScalarValue_weight_lipschitz P hP hlam hrho) hbase
    _ = _ := by ring

/-- On an offer cap `H`, the preceding constant is at most `2(H+1)`, uniformly
in the number of variables. -/
theorem normalizedScalarGap_weight_lipschitz_of_bounded {n : ℕ} (P : Instance n)
    {H : ℝ} (hH : 0 ≤ H) (hBound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    {lam rho : ℝ} (hlam : lam ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 1) :
    |normalizedScalarGap P lam - normalizedScalarGap P rho| ≤
      2 * (H + 1) * |lam - rho| := by
  have hM := P.expectedMaximum_le_of_bounded hH hBound
  have h := normalizedScalarGap_weight_lipschitz P (P.integrable_maximum_of_bounded hBound) hlam hrho
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith : 2 * (P.expectedMaximum + 1) ≤ 2 * (H + 1))
    (abs_nonneg _))

end ProphetSecretary.Model
