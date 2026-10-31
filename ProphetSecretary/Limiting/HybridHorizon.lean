import ProphetSecretary.Limiting.HybridIntensityComparison

/-!
# Remaining-horizon states of a finite-intensity hybrid instance

Rescaling a remaining horizon u keeps the retained laws and terminal reward,
multiplies anonymous intensity by u, and gives normalized duration weight cu.
In particular the value at u=0 need not vanish: the retained offers remain.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def FiniteIntensityHybridInstance.remainingHorizon (B : FiniteIntensityHybridInstance n) (u : ℝ≥0) :
    FiniteIntensityHybridInstance n where
  cap := B.cap
  terminal := B.terminal
  terminal_le_cap := B.terminal_le_cap
  individuals := B.individuals
  individual_bounded := B.individual_bounded
  intensity := u • B.intensity
  intensity_supported := Measure.ae_smul_measure B.intensity_supported u

noncomputable def FiniteIntensityHybridInstance.continuationValue (B : FiniteIntensityHybridInstance n)
    (w c : ℝ) (u : ℝ≥0) : ℝ := (B.remainingHorizon u).optimalScalarValue w (c*(u : ℝ))

lemma FiniteIntensityHybridInstance.remainingHorizon_intensity_mono (B : FiniteIntensityHybridInstance n)
    {u v : ℝ≥0} (h : u ≤ v) :
    ((B.remainingHorizon u).intensity : Measure ℝ) ≤ ((B.remainingHorizon v).intensity : Measure ℝ) := by
  intro A
  change (u : ℝ≥0∞)*(B.intensity : Measure ℝ) A ≤ (v : ℝ≥0∞)*(B.intensity : Measure ℝ) A
  exact mul_le_mul' (by exact_mod_cast h) le_rfl

lemma FiniteIntensityHybridInstance.remainingHorizon_value_mono_intensity (B : FiniteIntensityHybridInstance n)
    {u v : ℝ≥0} (h : u ≤ v) {w d : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d) :
    (B.remainingHorizon u).optimalScalarValue w d ≤ (B.remainingHorizon v).optimalScalarValue w d :=
  (B.remainingHorizon u).optimalScalarValue_mono_intensity (B.remainingHorizon v) le_rfl rfl rfl
    (B.remainingHorizon_intensity_mono h) hw hd

lemma FiniteIntensityHybridInstance.exists_policy_near_value (B : FiniteIntensityHybridInstance n)
    (w c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ π : RandomizedHybridPolicy n, B.optimalScalarValue w c-ε < π.scalarObjective B w c := by
  obtain ⟨x,hx,hlt⟩ := exists_lt_of_lt_csSup (B.scalarPayoffs_nonempty w c)
    (show B.optimalScalarValue w c-ε < sSup (B.scalarPayoffs w c) by change B.optimalScalarValue w c-ε < B.optimalScalarValue w c; linarith)
  obtain ⟨π,rfl⟩ := hx
  exact ⟨π,hlt⟩

lemma FiniteIntensityHybridInstance.optimalScalarValue_mono_duration (B : FiniteIntensityHybridInstance n)
    (w : ℝ) {d e : ℝ} (h : d ≤ e) : B.optimalScalarValue w d ≤ B.optimalScalarValue w e := by
  apply csSup_le (B.scalarPayoffs_nonempty w d)
  rintro _ ⟨π,rfl⟩
  exact (show π.scalarObjective B w d ≤ π.scalarObjective B w e by
    rw [π.scalarObjective_eq,π.scalarObjective_eq]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right h (π.expectedDuration_nonnegative B))).trans
      (B.scalarObjective_le_value π w e)

lemma FiniteIntensityHybridInstance.continuationValue_mono (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) : Monotone (B.continuationValue w c) := by
  intro u v huv
  exact ((B.remainingHorizon u).optimalScalarValue_mono_duration w
    (mul_le_mul_of_nonneg_left (by exact_mod_cast huv) hc)).trans
      (B.remainingHorizon_value_mono_intensity huv hw (mul_nonneg hc v.property))

end ProphetSecretary.Limiting
