import ProphetSecretary.Model.ScalarIntervalMinimizer
import ProphetSecretary.Model.UnitScalarGap

/-!
# Actual minima of normalized scalar gaps

The manuscript's W(P) is the minimum on [0,1], and W_I(P) is the minimum
on the specified compact interval. Both are defined by the actual scalar
gap, with attainment proved from continuity. No minimizer is assumed as
an interface. Boundary slack bounds W_I by a uniform multiple of W.
-/

open MeasureTheory Set
namespace ProphetSecretary.Model
variable {n : ℕ}

noncomputable def intervalNormalizedScalarGapMinimum (P : Instance n) (lo hi : ℝ) : ℝ :=
  sInf (normalizedScalarGap P '' Icc lo hi)

noncomputable def minimumNormalizedScalarGap (P : Instance n) : ℝ :=
  intervalNormalizedScalarGapMinimum P 0 1

lemma intervalNormalizedScalarGap_bddBelow (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    {lo hi : ℝ} (h0 : 0≤lo) (h1 : hi≤1) :
    BddBelow (normalizedScalarGap P '' Icc lo hi) := by
  refine ⟨0,?_⟩
  rintro _ ⟨a,ha,rfl⟩
  exact normalizedScalarGap_nonnegative P hP ⟨h0.trans ha.1,ha.2.trans h1⟩

lemma intervalNormalizedScalarGapMinimum_le (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    {lo hi a : ℝ} (h0 : 0≤lo) (h1 : hi≤1) (ha : a∈Icc lo hi) :
    intervalNormalizedScalarGapMinimum P lo hi≤normalizedScalarGap P a :=
  csInf_le (intervalNormalizedScalarGap_bddBelow P hP h0 h1) ⟨a,ha,rfl⟩

lemma intervalNormalizedScalarGapMinimum_attained (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    {lo hi : ℝ} (h0 : 0≤lo) (h1 : hi≤1) (hlohi : lo≤hi) :
    ∃ a∈Icc lo hi, normalizedScalarGap P a=intervalNormalizedScalarGapMinimum P lo hi := by
  obtain ⟨a,ha,hMin⟩ := P.normalizedScalarGap_exists_interval_minimizer hP h0 h1 hlohi
  refine ⟨a,ha,le_antisymm ?_ (intervalNormalizedScalarGapMinimum_le P hP h0 h1 ha)⟩
  change normalizedScalarGap P a≤sInf (normalizedScalarGap P '' Icc lo hi)
  have hNonempty : (normalizedScalarGap P '' Icc lo hi).Nonempty := ⟨normalizedScalarGap P a,a,ha,rfl⟩
  apply le_csInf hNonempty
  rintro _ ⟨b,hb,rfl⟩
  exact hMin b hb

lemma minimumNormalizedScalarGap_attained (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    ∃ a∈Icc (0 : ℝ) 1, normalizedScalarGap P a=minimumNormalizedScalarGap P :=
  intervalNormalizedScalarGapMinimum_attained P hP le_rfl le_rfl zero_le_one

lemma intervalNormalizedScalarGapMinimum_mem_unit (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {lo hi : ℝ} (h0 : 0≤lo) (h1 : hi≤1) (hlohi : lo≤hi) :
    intervalNormalizedScalarGapMinimum P lo hi∈Icc (0 : ℝ) 1 := by
  obtain ⟨a,ha,hEq⟩ := intervalNormalizedScalarGapMinimum_attained P
    (P.integrable_maximum_of_bounded hcap) h0 h1 hlohi
  rw [← hEq]
  exact P.normalizedScalarGap_mem_unit hcap ⟨h0.trans ha.1,ha.2.trans h1⟩

theorem intervalNormalizedScalarGapMinimum_le_global_of_outside_slack (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {lo hi d : ℝ}
    (h0 : 0≤lo) (h1 : hi≤1) (hlohi : lo≤hi) (hd : 0<d)
    (hOutside : ∀ a∈Icc (0 : ℝ) 1, a∉Icc lo hi → d≤normalizedScalarGap P a) :
    intervalNormalizedScalarGapMinimum P lo hi≤(1+1/d)*minimumNormalizedScalarGap P := by
  have hP := P.integrable_maximum_of_bounded hcap
  obtain ⟨a,ha,hEq⟩ := minimumNormalizedScalarGap_attained P hP
  have hW0 : 0≤minimumNormalizedScalarGap P := by
    rw [← hEq]
    exact (P.normalizedScalarGap_mem_unit hcap ha).1
  have hMul : minimumNormalizedScalarGap P/d≤(1+1/d)*minimumNormalizedScalarGap P := by
    calc
      _ = (1/d)*minimumNormalizedScalarGap P := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith : 1/d≤1+1/d) hW0
  by_cases hInside : a∈Icc lo hi
  · have hI := intervalNormalizedScalarGapMinimum_le P hP h0 h1 hInside
    rw [hEq] at hI
    have hGrow : minimumNormalizedScalarGap P≤(1+1/d)*minimumNormalizedScalarGap P := by
      have h := mul_nonneg (one_div_nonneg.mpr hd.le) hW0
      nlinarith only [h]
    exact hI.trans hGrow
  · have hLower : d≤minimumNormalizedScalarGap P := hEq ▸ hOutside a ha hInside
    have hDiv : (1 : ℝ)≤minimumNormalizedScalarGap P/d :=
      (le_div_iff₀ hd).mpr (by simpa only [one_mul] using hLower)
    exact (intervalNormalizedScalarGapMinimum_mem_unit P hcap h0 h1 hlohi).2.trans (hDiv.trans hMul)

end ProphetSecretary.Model
