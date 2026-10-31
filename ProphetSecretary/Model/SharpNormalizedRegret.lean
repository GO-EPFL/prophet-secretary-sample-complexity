import ProphetSecretary.Model.MidpointRegret
import ProphetSecretary.Model.CompetitiveBasic

/-!
# Sharp changes of true regret in the scalar weight

All admissible randomized policies have reward-duration slopes in [-1,M]. The
actual unrestricted value supremum has the same secant bounds. Their difference
therefore has Lipschitz constant M+1, bounded by H+1 on cap-H instances.
Paper correspondence: finite ingredient of `lem:scalar-clamp`. The bound requires no endpoint-slack hypothesis.
-/

open MeasureTheory Set
namespace ProphetSecretary.Model
variable {n : ℕ}

lemma RandomizedPolicy.normalizedObjective_secant_bounds (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {x y : ℝ} (hxy : x≤y) :
    -(y-x)≤π.scalarObjective P y (1-y)-π.scalarObjective P x (1-x) ∧
      π.scalarObjective P y (1-y)-π.scalarObjective P x (1-x)≤P.expectedMaximum*(y-x) := by
  have hR0 := π.expectedReward_nonnegative P
  have hRM := π.expectedReward_le_maximum P hP
  have hT0 := π.expectedDuration_nonnegative P
  have hT1 := π.expectedDuration_le_one P
  have hLow := mul_le_mul_of_nonneg_left (show -1≤π.expectedReward P-π.expectedDuration P by linarith) (sub_nonneg.mpr hxy)
  have hHigh := mul_le_mul_of_nonneg_left (show π.expectedReward P-π.expectedDuration P≤P.expectedMaximum by linarith) (sub_nonneg.mpr hxy)
  rw [π.scalarObjective_eq P hP,π.scalarObjective_eq P hP]
  constructor <;> nlinarith only [hLow,hHigh]

/-- Secants of the unrestricted value inherit the fixed-policy slope interval.
No optimizer, Markov restriction, or finite-support approximation is used. -/
lemma normalizedValue_secant_bounds (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    {x y : ℝ} (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) (hxy : x≤y) :
    -(y-x)≤optimalScalarValue P y (1-y)-optimalScalarValue P x (1-x) ∧
      optimalScalarValue P y (1-y)-optimalScalarValue P x (1-x)≤P.expectedMaximum*(y-x) := by
  have hUpper : optimalScalarValue P y (1-y)≤optimalScalarValue P x (1-x)+P.expectedMaximum*(y-x) := by
    apply csSup_le (scalarValues_nonempty P y (1-y))
    rintro v ⟨π,rfl⟩
    have h := (π.normalizedObjective_secant_bounds P hP hxy).2
    have hv := scalarObjective_le_optimal π P hP hx.1 (sub_nonneg.mpr hx.2)
    linarith only [h,hv]
  have hLower : optimalScalarValue P x (1-x)≤optimalScalarValue P y (1-y)+(y-x) := by
    apply csSup_le (scalarValues_nonempty P x (1-x))
    rintro v ⟨π,rfl⟩
    have h := (π.normalizedObjective_secant_bounds P hP hxy).1
    have hv := scalarObjective_le_optimal π P hP hy.1 (sub_nonneg.mpr hy.2)
    linarith only [h,hv]
  constructor <;> linarith only [hUpper,hLower]

/-- Sharp true-regret constant, valid for every general admissible policy. -/
theorem RandomizedPolicy.normalizedRegret_weight_lipschitz (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam rho : ℝ}
    (hlam : lam∈Icc (0:ℝ) 1) (hrho : rho∈Icc (0:ℝ) 1) :
    |π.normalizedRegret P lam-π.normalizedRegret P rho|≤(P.expectedMaximum+1)*|lam-rho| := by
  have hOrdered (x y : ℝ) (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) (hxy : x≤y) :
      |π.normalizedRegret P y-π.normalizedRegret P x|≤(P.expectedMaximum+1)*(y-x) := by
    have hV := normalizedValue_secant_bounds P hP hx hy hxy
    have hJ := π.normalizedObjective_secant_bounds P hP hxy
    rw [abs_le]
    unfold normalizedRegret
    constructor <;> nlinarith only [hV.1,hV.2,hJ.1,hJ.2]
  rcases le_total lam rho with h | h
  · rw [abs_sub_comm (π.normalizedRegret P lam) (π.normalizedRegret P rho),abs_of_nonpos (sub_nonpos.mpr h)]
    have hB := hOrdered lam rho hlam hrho h
    nlinarith only [hB]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact hOrdered rho lam hrho hlam h

/-- The cap-only constant is independent of the finite instance size. -/
theorem RandomizedPolicy.normalizedRegret_weight_lipschitz_of_bounded (π : RandomizedPolicy n) (P : Instance n)
    {H : ℝ} (hH : 0≤H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤H) {lam rho : ℝ}
    (hlam : lam∈Icc (0:ℝ) 1) (hrho : rho∈Icc (0:ℝ) 1) :
    |π.normalizedRegret P lam-π.normalizedRegret P rho|≤(H+1)*|lam-rho| := by
  have h := π.normalizedRegret_weight_lipschitz P (P.integrable_maximum_of_bounded hcap) hlam hrho
  have hM := P.expectedMaximum_le_of_bounded hH hcap
  exact h.trans (mul_le_mul_of_nonneg_right (show P.expectedMaximum+1≤H+1 by linarith only [hM]) (abs_nonneg _))

/-- The projection loss before any boundary slack is supplied. -/
lemma RandomizedPolicy.scalarGap_ge_gap_sub_projectedRegret (π : RandomizedPolicy n) (P : Instance n)
    {H : ℝ} (hH : 0≤H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤H) {lam rho r : ℝ}
    (hlam : lam∈Icc (0:ℝ) 1) (hrho : rho∈Icc (0:ℝ) 1) (hr : π.normalizedRegret P rho≤r) :
    normalizedScalarGap P lam-r-(H+1)*|lam-rho|≤
      π.scalarObjective P lam (1-lam)-optimalCompetitiveRatio*(lam*P.expectedMaximum+1-lam) := by
  have hRegret := (abs_le.mp (π.normalizedRegret_weight_lipschitz_of_bounded P hH hcap hlam hrho)).2
  unfold normalizedScalarGap scalarGap normalizedRegret at *
  linarith only [hRegret,hr]

end ProphetSecretary.Model
