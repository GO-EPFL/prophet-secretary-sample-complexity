import ProphetSecretary.Analysis.DyadicChaining

/-! # Chaining when measurability is specified only on the interval
Zero extension outside `[0,1]` supplies a total process without adding any
assumption on values that are absent from the supremum and moment hypotheses.
-/
open MeasureTheory Set
open scoped Topology
namespace ProphetSecretary.Analysis
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def intervalProcessExtension (f : Ω → ℝ → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  if t ∈ Icc (0 : ℝ) 1 then f ω t else 0

omit [MeasurableSpace Ω] in
lemma intervalProcessExtension_of_mem (f : Ω → ℝ → ℝ) (ω : Ω) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    intervalProcessExtension f ω t = f ω t := if_pos ht

theorem continuous_interval_supremum_moment (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ → ℝ} (hf : ∀ t ∈ Icc (0 : ℝ) 1, Measurable (fun ω ↦ f ω t))
    {D B : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hBound : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D)
    (hCont : ∀ᵐ ω ∂μ, ContinuousOn (f ω) (Icc (0 : ℝ) 1)) (p : ℕ) (hp : 2 ≤ p)
    (hMoment : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ ω, |f ω s - f ω t| ^ p ∂μ) ≤ B * |s - t| ^ p) :
    ∃ S : Ω → ℝ, Measurable S ∧
      (∀ᵐ ω ∂μ, S ω = sSup {y : ℝ | ∃ t ∈ Icc (0 : ℝ) 1, y = |f ω t|}) ∧
      Integrable (fun ω ↦ S ω ^ p) μ ∧
      (∫ ω, S ω ^ p ∂μ) ≤ dyadicChainingConstant p *
        ((∫ ω, |f ω 0| ^ p ∂μ) + (∫ ω, |f ω 1| ^ p ∂μ) + B) := by
  let F := intervalProcessExtension f
  have hMeas (t : ℝ) : Measurable (fun ω ↦ F ω t) := by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · simpa only [F, intervalProcessExtension, if_pos ht] using hf t ht
    · simp only [F, intervalProcessExtension, if_neg ht]
      exact measurable_const
  have hBoundF : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |F ω t| ≤ D :=
    hBound.mono (fun ω hω t ht ↦ by simpa only [F, intervalProcessExtension_of_mem f ω ht] using hω t ht)
  have hContF : ∀ᵐ ω ∂μ, ContinuousOn (F ω) (Icc (0 : ℝ) 1) := by
    filter_upwards [hCont] with ω hω
    exact hω.congr (fun t ht ↦ intervalProcessExtension_of_mem f ω ht)
  have hMomentF : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ ω, |F ω s - F ω t| ^ p ∂μ) ≤ B * |s - t| ^ p := by
    intro s hs t ht
    simpa only [F, intervalProcessExtension_of_mem f _ hs, intervalProcessExtension_of_mem f _ ht] using hMoment s hs t ht
  obtain ⟨hM, hEq, hI, hRate⟩ := continuous_dyadic_chaining μ hMeas hD hB hBoundF hContF p hp hMomentF
  refine ⟨dyadicSupremum F, hM, ?_, hI, ?_⟩
  · filter_upwards [hEq] with ω hω
    rw [hω]
    congr 1
    ext y
    constructor <;> rintro ⟨t, ht, hy⟩
    · exact ⟨t, ht, by simpa only [F, intervalProcessExtension_of_mem f ω ht] using hy⟩
    · exact ⟨t, ht, by simpa only [F, intervalProcessExtension_of_mem f ω ht] using hy⟩
  · simpa only [F, intervalProcessExtension_of_mem f _ (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩),
      intervalProcessExtension_of_mem f _ (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)] using hRate

end ProphetSecretary.Analysis
