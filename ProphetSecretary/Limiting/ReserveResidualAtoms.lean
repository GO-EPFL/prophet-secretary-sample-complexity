import ProphetSecretary.Limiting.ContinuousWeightedResidualLimit
import ProphetSecretary.Limiting.ReserveIntensityFromWeight

/-!
# Every common continuity level above the reserve

The initial finite weighted aggregate has a null atom at b>a exactly when
all retained individual laws and the constructed reserve intensity do. The
cutoff condition therefore matches the manuscript's full quantifier.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Limiting

lemma continuousWeighted_prefixResidual_le_initial (w : ℝ →ᵇ ℝ) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1)) (N : ℕ) :
    (ρ N : Measure ℝ) ≤ (ρ 0 : Measure ℝ) := by
  apply Measure.le_iff.mpr
  intro s hs
  have hp := continuousWeighted_residual_prefix_identity w Q ρ hρ N
  have he := congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ) s) hp
  rw [FiniteMeasure.toMeasure_add,Measure.add_apply] at he
  rw [he]
  exact le_add_of_nonneg_left (show (0 : ENNReal) ≤
    (↑(∑ i ∈ Finset.range N, continuousWeightedLaw (Q i) w) : Measure ℝ) s from bot_le)

lemma continuousWeighted_prefixResidual_atom_zero (w : ℝ →ᵇ ℝ) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1))
    {b : ℝ} (hatom : (ρ 0 : Measure ℝ) {b} = 0) (N : ℕ) : (ρ N : Measure ℝ) {b} = 0 := by
  have h := Measure.le_iff.mp (continuousWeighted_prefixResidual_le_initial w Q ρ hρ N) {b} (measurableSet_singleton b)
  rw [hatom] at h
  exact le_antisymm h bot_le

lemma reserveMarkIntensity_atom_zero_iff (η : FiniteMeasure ℝ) (w : ℝ →ᵇ ℝ)
    {a b : ℝ} (hb : a < b) (hwb : 0 < w b) :
    reserveMarkIntensity η w a {b} = 0 ↔ (η : Measure ℝ) {b} = 0 := by
  rw [reserveMarkIntensity,withDensity_apply _ (measurableSet_singleton b),lintegral_singleton,
    reserveReciprocalWeight,if_pos hb,mul_eq_zero]
  have hnonzero : ENNReal.ofReal (1/w b) ≠ 0 := (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hwb)).ne'
  simp only [hnonzero,false_or]

lemma continuousWeightedLaw_atom_zero_iff (p : ProbabilityMeasure ℝ) (w : ℝ →ᵇ ℝ)
    {b : ℝ} (hwb : 0 < w b) :
    (continuousWeightedLaw p w : Measure ℝ) {b} = 0 ↔ (p : Measure ℝ) {b} = 0 := by
  change (p : Measure ℝ).withDensity (fun x => ENNReal.ofReal (w x)) {b} = 0 ↔ _
  rw [withDensity_apply _ (measurableSet_singleton b),lintegral_singleton,mul_eq_zero]
  simp only [(ENNReal.ofReal_pos.mpr hwb).ne',false_or]

lemma continuousWeighted_common_atom_zero_of_initial (w : ℝ →ᵇ ℝ) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1))
    {a b : ℝ} (hb : a < b) (hwb : 0 < w b) (hatom : (ρ 0 : Measure ℝ) {b} = 0) :
    (∀ i, (Q i : Measure ℝ) {b} = 0) ∧
      reserveMarkIntensity (extractedContinuousWeightedResidual w Q ρ) w a {b} = 0 := by
  constructor
  · intro i
    have hρi := continuousWeighted_prefixResidual_atom_zero w Q ρ hρ hatom i
    have he := congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ) {b}) (hρ i)
    rw [FiniteMeasure.toMeasure_add,Measure.add_apply,hρi] at he
    apply (continuousWeightedLaw_atom_zero_iff _ w hwb).mp
    have hle : (continuousWeightedLaw (Q i) w : Measure ℝ) {b} ≤ 0 :=
      (le_add_of_nonneg_right (show (0 : ENNReal) ≤ (ρ (i+1) : Measure ℝ) {b} from bot_le)).trans_eq he.symm
    exact le_antisymm hle bot_le
  · apply (reserveMarkIntensity_atom_zero_iff _ w hb hwb).mpr
    have h := Measure.le_iff.mp (extractedContinuousWeightedResidual_le_initial w Q ρ) {b} (measurableSet_singleton b)
    rw [hatom] at h
    exact le_antisymm h bot_le

lemma continuousWeighted_initial_atom_zero_of_common (w : ℝ →ᵇ ℝ) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1))
    {a b : ℝ} (hb : a < b) (hwb : 0 < w b) (hQ : ∀ i, (Q i : Measure ℝ) {b} = 0)
    (hμ : reserveMarkIntensity (extractedContinuousWeightedResidual w Q ρ) w a {b} = 0) :
    (ρ 0 : Measure ℝ) {b} = 0 := by
  have hη := (reserveMarkIntensity_atom_zero_iff _ w hb hwb).mp hμ
  have hsum : retainedContinuousWeightedMeasure w Q {b} = 0 := by
    apply Measure.sum_apply_eq_zero.mpr
    intro i
    exact (withDensity_absolutelyContinuous _ _) (hQ i)
  have he := congrArg (fun ν : Measure ℝ => ν {b}) (extractedContinuousWeightedResidual_add_retained w Q ρ hρ)
  rw [Measure.add_apply,hη,hsum,zero_add] at he
  exact he.symm

end ProphetSecretary.Limiting
