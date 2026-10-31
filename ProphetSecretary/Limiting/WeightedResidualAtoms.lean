import ProphetSecretary.Limiting.WeightedResidualLimit
import ProphetSecretary.Limiting.PositiveIntensityFromWeight

/-!
# Common continuity levels of extracted marginal and residual measures

Every finite-prefix residual and every retained weighted marginal is dominated
by the initial weighted aggregate limit. Above zero, its null atoms are exactly
the common null atoms of all individual laws and the constructed positive-mark
intensity. This preserves the continuity-level quantifier in the manuscript.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

lemma extracted_prefixResidual_le_initial (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = valueWeightedLaw (Q N) H + ρ (N+1)) (N : ℕ) :
    (ρ N : Measure ℝ) ≤ (ρ 0 : Measure ℝ) := by
  apply Measure.le_iff.mpr
  intro s hs
  have hp := extracted_residual_prefix_identity H Q ρ hρ N
  have he := congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ) s) hp
  rw [FiniteMeasure.toMeasure_add,Measure.add_apply] at he
  rw [he]
  exact le_add_of_nonneg_left (show (0 : ENNReal) ≤
    (↑(∑ i ∈ Finset.range N, valueWeightedLaw (Q i) H) : Measure ℝ) s from bot_le)

lemma extracted_prefixResidual_atom_zero (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = valueWeightedLaw (Q N) H + ρ (N+1))
    {b : ℝ} (hatom : (ρ 0 : Measure ℝ) {b} = 0) (N : ℕ) : (ρ N : Measure ℝ) {b} = 0 := by
  have h := Measure.le_iff.mp (extracted_prefixResidual_le_initial H Q ρ hρ N) {b} (measurableSet_singleton b)
  rw [hatom] at h
  exact le_antisymm h bot_le

lemma extracted_weightedResidual_atom_zero (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) {b : ℝ} (hatom : (ρ 0 : Measure ℝ) {b} = 0) :
    (extractedWeightedResidual H Q ρ : Measure ℝ) {b} = 0 := by
  have h := Measure.le_iff.mp (extractedWeightedResidual_le_initial H Q ρ) {b} (measurableSet_singleton b)
  rw [hatom] at h
  exact le_antisymm h bot_le

lemma positiveMarkIntensity_atom_zero_iff (η : FiniteMeasure ℝ) {b : ℝ} (hb : 0 < b) :
    positiveMarkIntensity η {b} = 0 ↔ (η : Measure ℝ) {b} = 0 := by
  rw [positiveMarkIntensity,withDensity_apply _ (measurableSet_singleton b),lintegral_singleton,
    positiveReciprocalWeight,if_pos hb,mul_eq_zero]
  have hnonzero : ENNReal.ofReal (1/b) ≠ 0 := (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hb)).ne'
  simp only [hnonzero,false_or]

lemma valueWeightedLaw_atom_zero_implies (p : ProbabilityMeasure ℝ) (H : ℝ≥0)
    (hcap : (p : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) {b : ℝ} (hb : 0 < b)
    (hatom : (valueWeightedLaw p H : Measure ℝ) {b} = 0) : (p : Measure ℝ) {b} = 0 := by
  by_cases hbH : b ≤ (H : ℝ)
  · change (p : Measure ℝ).withDensity (fun x => ENNReal.ofReal (boundedOfferValue H x)) {b} = 0 at hatom
    rw [withDensity_apply _ (measurableSet_singleton b),lintegral_singleton,
      boundedOfferValue_eq H ⟨hb.le,hbH⟩,mul_eq_zero] at hatom
    exact hatom.resolve_left (ENNReal.ofReal_pos.mpr hb).ne'
  · apply measure_mono_null _ hcap
    intro x hx hmem
    have hxb : x = b := Set.mem_singleton_iff.mp hx
    subst x
    exact hbH hmem.2

/-- Every positive null atom of the initial aggregate is a simultaneous
continuity level of all retained laws and the residual intensity. -/
lemma extracted_common_atom_zero_of_initial (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = valueWeightedLaw (Q N) H + ρ (N+1))
    (hQ : ∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0)
    {b : ℝ} (hb : 0 < b) (hatom : (ρ 0 : Measure ℝ) {b} = 0) :
    (∀ i, (Q i : Measure ℝ) {b} = 0) ∧ positiveMarkIntensity (extractedWeightedResidual H Q ρ) {b} = 0 := by
  constructor
  · intro i
    have hρi := extracted_prefixResidual_atom_zero H Q ρ hρ hatom i
    have he := congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ) {b}) (hρ i)
    rw [FiniteMeasure.toMeasure_add,Measure.add_apply,hρi] at he
    have hwi : (valueWeightedLaw (Q i) H : Measure ℝ) {b} = 0 := by
      have hle : (valueWeightedLaw (Q i) H : Measure ℝ) {b} ≤ 0 :=
        (le_add_of_nonneg_right (show (0 : ENNReal) ≤ (ρ (i+1) : Measure ℝ) {b} from bot_le)).trans_eq he.symm
      exact le_antisymm hle bot_le
    exact valueWeightedLaw_atom_zero_implies _ H (hQ i) hb hwi
  · exact (positiveMarkIntensity_atom_zero_iff _ hb).mpr (extracted_weightedResidual_atom_zero H Q ρ hatom)

/-- Conversely, the paper's common continuity-level condition suffices for
nullity of the initial weighted aggregate atom. -/
lemma extracted_initial_atom_zero_of_common (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = valueWeightedLaw (Q N) H + ρ (N+1))
    {b : ℝ} (hb : 0 < b) (hQ : ∀ i, (Q i : Measure ℝ) {b} = 0)
    (hμ : positiveMarkIntensity (extractedWeightedResidual H Q ρ) {b} = 0) :
    (ρ 0 : Measure ℝ) {b} = 0 := by
  have hη := (positiveMarkIntensity_atom_zero_iff _ hb).mp hμ
  have hsum : retainedWeightedMeasure H Q {b} = 0 := by
    apply Measure.sum_apply_eq_zero.mpr
    intro i
    exact (withDensity_absolutelyContinuous _ _) (hQ i)
  have he := congrArg (fun ν : Measure ℝ => ν {b}) (extractedWeightedResidual_add_retained H Q ρ hρ)
  rw [Measure.add_apply,hη,hsum,zero_add] at he
  exact he.symm

end ProphetSecretary.Limiting
