import ProphetSecretary.Reach.Robust
import ProphetSecretary.Model.BellmanBase
import ProphetSecretary.Model.ScalarValueProperties

/-!
# The instance scalar ratio used as a calibration target

The quantity in `eq:calibration-ratio` minimizes over weights for one fixed
instance. It differs from the global competitive ratio, which also takes an
infimum over instances. Positive expected maximum keeps every denominator
positive, including the reward endpoint.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- Scalar competitive ratio of a fixed instance and normalized weight. -/
noncomputable def Instance.normalizedScalarRatio (P : Instance n) (lam : ℝ) : ℝ :=
  optimalScalarValue P lam (1 - lam) / (lam * P.expectedMaximum + 1 - lam)

/-- The full-information ratio used by duration calibration. -/
noncomputable def Instance.optimalScalarRatio (P : Instance n) : ℝ :=
  sInf (P.normalizedScalarRatio '' Icc (0 : ℝ) 1)

lemma Instance.scalarRatio_denominator_pos (P : Instance n) (hM : 0 < P.expectedMaximum)
    {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) 1) :
    0 < lam * P.expectedMaximum + 1 - lam := by
  by_cases hz : lam = 0
  · simp [hz]
  · have hp : 0 < lam * P.expectedMaximum := mul_pos (lt_of_le_of_ne hlam.1 (Ne.symm hz)) hM
    linarith [hlam.2]

lemma Instance.normalizedScalarRatio_continuousOn (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) :
    ContinuousOn P.normalizedScalarRatio (Icc (0 : ℝ) 1) := by
  apply (optimalScalarValue_weight_continuousOn P hP.1).div
    (show ContinuousOn (fun lam : ℝ => lam * P.expectedMaximum + 1 - lam) (Icc 0 1) from by fun_prop)
  intro lam hlam
  exact (P.scalarRatio_denominator_pos hP.2 hlam).ne'

@[simp] lemma Instance.normalizedScalarRatio_zero (P : Instance n) :
    P.normalizedScalarRatio 0 = 1 := by
  simp [Instance.normalizedScalarRatio, optimalScalarValue_zero_rewardWeight P zero_le_one]

lemma Instance.competitiveRatio_le_normalizedScalarRatio (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) 1) :
    optimalCompetitiveRatio ≤ P.normalizedScalarRatio lam := by
  apply (le_div_iff₀ (P.scalarRatio_denominator_pos hP.2 hlam)).mpr
  have h := globalScalar_inequality_of_integrable P hP.1 hlam.1 (sub_nonneg.mpr hlam.2)
  simpa only [add_sub_assoc] using h

/-- A minimizing weight is deterministic for the true instance, before training. -/
theorem Instance.exists_scalarRatio_minimizer (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) :
    ∃ lam ∈ Icc (0 : ℝ) 1,
      P.optimalScalarRatio = P.normalizedScalarRatio lam ∧
      ∀ nu ∈ Icc (0 : ℝ) 1, P.normalizedScalarRatio lam ≤ P.normalizedScalarRatio nu := by
  obtain ⟨lam, hlam, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)) (P.normalizedScalarRatio_continuousOn hP)
  have hleast : IsLeast (P.normalizedScalarRatio '' Icc (0 : ℝ) 1)
      (P.normalizedScalarRatio lam) := by
    refine ⟨⟨lam, hlam, rfl⟩, ?_⟩
    rintro _ ⟨nu, hnu, rfl⟩
    exact hmin hnu
  refine ⟨lam, hlam, ?_, fun nu hnu => hmin hnu⟩
  exact hleast.csInf_eq

/-- The target ratio lies between the global ratio and one. -/
theorem Instance.optimalScalarRatio_bounds (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) :
    optimalCompetitiveRatio ≤ P.optimalScalarRatio ∧ P.optimalScalarRatio ≤ 1 := by
  obtain ⟨lam, hlam, heq, hmin⟩ := P.exists_scalarRatio_minimizer hP
  rw [heq]
  refine ⟨P.competitiveRatio_le_normalizedScalarRatio hP hlam, ?_⟩
  simpa using hmin 0 (by norm_num)

/-- The gap at a ratio-minimizing weight is exactly the ratio slack times
its benchmark denominator. -/
theorem Instance.normalizedScalarGap_at_ratio_minimizer (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) 1)
    (hmin : P.optimalScalarRatio = P.normalizedScalarRatio lam) :
    normalizedScalarGap P lam = (P.optimalScalarRatio - optimalCompetitiveRatio) *
      (lam * P.expectedMaximum + 1 - lam) := by
  rw [hmin]
  unfold Instance.normalizedScalarRatio normalizedScalarGap scalarGap
  field_simp [(P.scalarRatio_denominator_pos hP.2 hlam).ne']
  ring

/-- Every normalized weight is bounded below by the minimizing ratio. -/
lemma Instance.optimalScalarRatio_le_at (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) 1) :
    P.optimalScalarRatio ≤ P.normalizedScalarRatio lam := by
  obtain ⟨rho, _, heq, hmin⟩ := P.exists_scalarRatio_minimizer hP
  rw [heq]
  exact hmin lam hlam

/-- Ratio slack is bounded by the normalized scalar gap divided by its benchmark. -/
lemma Instance.ratioSlack_mul_benchmark_le_gap (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) {lam : ℝ} (hlam : lam ∈ Icc (0 : ℝ) 1) :
    (P.optimalScalarRatio - optimalCompetitiveRatio) *
      (lam * P.expectedMaximum + 1 - lam) ≤ normalizedScalarGap P lam := by
  have h := (le_div_iff₀ (P.scalarRatio_denominator_pos hP.2 hlam)).mp
    (P.optimalScalarRatio_le_at hP hlam)
  unfold normalizedScalarGap scalarGap
  nlinarith

/-- The same ratio in duration-coefficient coordinates. -/
noncomputable def Instance.durationScalarRatio (P : Instance n) (z : ℝ) : ℝ :=
  optimalScalarValue P 1 z / (P.expectedMaximum + z)

lemma Instance.normalizedScalarRatio_eq_durationScalarRatio (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) {z : ℝ} (hz : 0 ≤ z) :
    P.normalizedScalarRatio (1 / (1 + z)) = P.durationScalarRatio z := by
  have hden : 1 + z ≠ 0 := by positivity
  have hM : P.expectedMaximum + z ≠ 0 := ne_of_gt (by linarith [hP.2])
  have hsub : 1 - 1 / (1 + z) = z / (1 + z) := by field_simp; ring
  have hb : (1 / (1 + z)) * P.expectedMaximum + 1 - 1 / (1 + z) =
      (P.expectedMaximum + z) / (1 + z) := by field_simp; ring
  unfold Instance.normalizedScalarRatio Instance.durationScalarRatio
  rw [hb, hsub, optimalScalarValue_normalize P hP.1 hz]
  field_simp

lemma Instance.optimalScalarRatio_le_durationScalarRatio (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) {z : ℝ} (hz : 0 ≤ z) :
    P.optimalScalarRatio ≤ P.durationScalarRatio z := by
  rw [← P.normalizedScalarRatio_eq_durationScalarRatio hP hz]
  apply P.optimalScalarRatio_le_at hP
  constructor
  · positivity
  · exact (div_le_one (by positivity : (0 : ℝ) < 1 + z)).mpr (by linarith)

/-- Waiting removes large duration coefficients from the clipped target search. -/
lemma Instance.durationScalarRatio_ge_fourFifths (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) {z : ℝ} (hz : 4 * P.expectedMaximum ≤ z) :
    4 / 5 ≤ P.durationScalarRatio z := by
  have hz0 : 0 ≤ z := by linarith [hP.2]
  apply (le_div_iff₀ (by linarith [hP.2] : 0 < P.expectedMaximum + z)).mpr
  have hwait := durationWeight_le_optimalScalarValue P hP.1 zero_le_one hz0
  linarith

/-- The reference weight for calibration can be fixed on a prescribed interval
before any training data are drawn. -/
theorem normalizedScalarGap_exists_minimizer_on (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∃ lam ∈ Icc a b, ∀ rho ∈ Icc a b,
      normalizedScalarGap P lam ≤ normalizedScalarGap P rho := by
  have hc := (normalizedScalarGap_continuousOn P hP).mono
    (fun (x : ℝ) (h : x ∈ Icc a b) => ⟨ha.trans h.1, h.2.trans hb⟩)
  obtain ⟨lam, hlam, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hc
  exact ⟨lam, hlam, fun rho hrho => hmin hrho⟩

lemma Instance.durationScalarRatio_le_one (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) {z : ℝ} (hz : 0 ≤ z) :
    P.durationScalarRatio z ≤ 1 := by
  apply (div_le_one (by linarith [hP.2] : 0 < P.expectedMaximum + z)).mpr
  simpa using optimalScalarValue_le_benchmark P hP.1 zero_le_one hz

/-- Both parametrizations in `eq:calibration-ratio` have the same infimum. -/
theorem Instance.optimalScalarRatio_eq_duration_infimum (P : Instance n)
    (hP : P.HasPositiveFiniteMaximum) :
    P.optimalScalarRatio = sInf (P.durationScalarRatio '' Ici (0 : ℝ)) := by
  have hn : (P.durationScalarRatio '' Ici (0 : ℝ)).Nonempty :=
    ⟨P.durationScalarRatio 0, 0, by simp, rfl⟩
  have hb : BddBelow (P.durationScalarRatio '' Ici (0 : ℝ)) := by
    refine ⟨P.optimalScalarRatio, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact P.optimalScalarRatio_le_durationScalarRatio hP hz
  apply le_antisymm
  · apply le_csInf hn
    rintro _ ⟨z, hz, rfl⟩
    exact P.optimalScalarRatio_le_durationScalarRatio hP hz
  · obtain ⟨lam, hlam, heq, _⟩ := P.exists_scalarRatio_minimizer hP
    by_cases hl0 : lam = 0
    · have hzero : P.optimalScalarRatio = 1 := by simpa [hl0] using heq
      rw [hzero]
      exact (csInf_le hb (show P.durationScalarRatio 0 ∈ P.durationScalarRatio '' Ici (0 : ℝ)
        from ⟨0, by simp, rfl⟩)).trans (P.durationScalarRatio_le_one hP le_rfl)
    · have hl : 0 < lam := lt_of_le_of_ne hlam.1 (Ne.symm hl0)
      let z := (1 - lam) / lam
      have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr hlam.2) hl.le
      have he : 1 / (1 + z) = lam := by dsimp [z]; field_simp; ring
      have hpoint := P.normalizedScalarRatio_eq_durationScalarRatio hP hz
      rw [he] at hpoint
      calc
        sInf (P.durationScalarRatio '' Ici (0 : ℝ)) ≤ P.durationScalarRatio z :=
          csInf_le hb ⟨z, hz, rfl⟩
        _ = P.normalizedScalarRatio lam := hpoint.symm
        _ = P.optimalScalarRatio := heq.symm

end ProphetSecretary.Model
