import ProphetSecretary.Limiting.DirectApproximationSchedule
import ProphetSecretary.Model.FiniteNormalizationBounds

/-!
# Actual normalized direct finite bases

Retain m+J individuals and use the already chosen virtual count at that same
index. A single tail index makes every base mean lie in [1/2,3/2]; J can be
increased later for a fixed individual or cutoff. Every law at parameter theta
is divided by this fixed base mean, not by its perturbed expected maximum.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

noncomputable def directNormalizationStart (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) : ℕ :=
  Classical.choose (exists_fixedBaseNormalization_tail
    (fun m => (B.directFiniteApproximation hZero m).expectedMaximum)
    (by simpa only [hMean] using B.directFiniteApproximation_expectedMaximum_tendsto hZero))

lemma directNormalizationStart_spec (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) :
    ∀ k≥B.directNormalizationStart hZero hMean,
      (B.directFiniteApproximation hZero k).expectedMaximum∈Icc (1/2 : ℝ) (3/2) :=
  Classical.choose_spec (exists_fixedBaseNormalization_tail
    (fun m => (B.directFiniteApproximation hZero m).expectedMaximum)
    (by simpa only [hMean] using B.directFiniteApproximation_expectedMaximum_tendsto hZero))

noncomputable def shiftedDirectSize (B : CountableInstance) (hZero : B.terminal=0) (J m : ℕ) : ℕ :=
  (m+J)+B.directVirtualCount hZero (m+J)

noncomputable def shiftedDirectBase (B : CountableInstance) (hZero : B.terminal=0) (J m : ℕ) :
    Instance (B.shiftedDirectSize hZero J m) := B.directFiniteApproximation hZero (m+J)

noncomputable def shiftedDirectMean (B : CountableInstance) (hZero : B.terminal=0) (J m : ℕ) : ℝ :=
  (B.shiftedDirectBase hZero J m).expectedMaximum

lemma shiftedDirectMean_range (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J) (m : ℕ) :
    B.shiftedDirectMean hZero J m∈Icc (1/2 : ℝ) (3/2) :=
  B.directNormalizationStart_spec hZero hMean (m+J) (by omega)

lemma shiftedDirectMean_positive (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J) (m : ℕ) :
    0<B.shiftedDirectMean hZero J m :=
  (fixedBaseNormalization_inverse_bound (B.shiftedDirectMean_range hZero hMean hJ m).1).1

/-- The same fixed base mean is used for every supplied perturbed law. -/
noncomputable def normalizeDirectInstance (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J)
    (m : ℕ) (Ptheta : Instance (B.shiftedDirectSize hZero J m)) : Instance (B.shiftedDirectSize hZero J m) :=
  Ptheta.scale (B.shiftedDirectMean hZero J m)⁻¹
    (inv_nonneg.mpr (B.shiftedDirectMean_positive hZero hMean hJ m).le)

noncomputable def normalizedDirectBase (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J)
    (m : ℕ) : Instance (B.shiftedDirectSize hZero J m) :=
  B.normalizeDirectInstance hZero hMean hJ m (B.shiftedDirectBase hZero J m)

noncomputable def normalizedDirectRewardWeight (B : CountableInstance) (hZero : B.terminal=0)
    (J : ℕ) (w c : ℝ) (m : ℕ) : ℝ := finiteNormalizationRewardWeight (B.shiftedDirectMean hZero J m) w c

noncomputable def normalizedDirectDurationWeight (B : CountableInstance) (hZero : B.terminal=0)
    (J : ℕ) (w c : ℝ) (m : ℕ) : ℝ := finiteNormalizationDurationWeight (B.shiftedDirectMean hZero J m) w c

lemma normalizedDirectBase_expectedMaximum (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J) (m : ℕ) :
    (B.normalizedDirectBase hZero hMean hJ m).expectedMaximum=1 :=
  (B.shiftedDirectBase hZero J m).fixedBaseNormalization_mean (B.shiftedDirectMean_positive hZero hMean hJ m)

lemma normalizeDirectInstance_cap (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J)
    (m : ℕ) (Ptheta : Instance (B.shiftedDirectSize hZero J m))
    (hCap : ∀ i, ∀ᵐ x ∂Ptheta.law i, x≤(B.cap : ℝ)) :
    ∀ i, ∀ᵐ x ∂(B.normalizeDirectInstance hZero hMean hJ m Ptheta).law i, x≤2*(B.cap : ℝ) :=
  Ptheta.fixedBaseNormalization_cap (B.shiftedDirectMean_range hZero hMean hJ m).1 B.cap.property hCap

lemma normalizedDirectBase_cap (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J) (m : ℕ) :
    ∀ i, ∀ᵐ x ∂(B.normalizedDirectBase hZero hMean hJ m).law i, x≤2*(B.cap : ℝ) :=
  B.normalizeDirectInstance_cap hZero hMean hJ m (B.shiftedDirectBase hZero J m)
    (B.directFiniteApproximation_bounded hZero (m+J))

lemma normalizedDirectBase_tailCount_le (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J)
    (m : ℕ) {b : ℝ} (hb : 0<b) :
    (B.normalizedDirectBase hZero hMean hJ m).tailCount b≤(B.totalTailMass (b/2)).toReal :=
  ((B.shiftedDirectBase hZero J m).fixedBaseNormalization_tailCount_le
    (B.shiftedDirectMean_range hZero hMean hJ m).1 hb.le).trans
      (B.directFiniteApproximation_tailCount_le hZero (m+J) (by positivity))

lemma normalizedDirectWeights_sum (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J)
    {w c : ℝ} (hw : 0<w) (hc : 0≤c) (m : ℕ) :
    B.normalizedDirectRewardWeight hZero J w c m+B.normalizedDirectDurationWeight hZero J w c m=1 :=
  (finiteNormalizationWeights (B.shiftedDirectMean_positive hZero hMean hJ m) hw hc).2.2

lemma normalizedDirectWeights_interior (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (hSum : w+c=1) (m : ℕ) :
    B.normalizedDirectRewardWeight hZero J w c m∈Icc (min w c/4) (1-min w c/4) :=
  (fixedBaseNormalization_weight_interval (B.shiftedDirectMean_range hZero hMean hJ m) hw hc hSum).2.2

end ProphetSecretary.Limiting.CountableInstance
