import ProphetSecretary.Probability.CountedMedian
import ProphetSecretary.Probability.ConfidenceLevel
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Confidence amplification by an actual iid median

The copy law is a literal finite product of the original experiment.
Powersets appear only in the probability proof; the returned median is the
counted insertion-sort procedure.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Probability

lemma failure_probability_le_of_mean_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (v h δ : ℝ) (hh : 0 < h)
    (hi : Integrable (fun q => (X q - v) ^ 2) μ)
    (he : (∫ q, (X q - v) ^ 2 ∂μ) ≤ δ * h ^ 2) :
    μ.real {q | h < |X q - v|} ≤ δ := by
  have hsub : {q | h < |X q - v|} ⊆ {q | h ^ 2 ≤ (X q - v) ^ 2} := by
    intro q hq
    have hs := (sq_le_sq₀ hh.le (abs_nonneg (X q - v))).2 hq.le
    simpa only [sq_abs, Set.mem_setOf_eq] using hs
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun q => sq_nonneg (X q - v))) hi (h ^ 2)
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hh)).mp
  calc
    h ^ 2 * μ.real {q | h < |X q - v|} ≤
        h ^ 2 * μ.real {q | h ^ 2 ≤ (X q - v) ^ 2} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub) (sq_nonneg h)
    _ ≤ ∫ q, (X q - v) ^ 2 ∂μ := hm
    _ ≤ h ^ 2 * δ := by nlinarith [he]

lemma failure_probability_le_one_sixtyFourth {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (v h : ℝ) (hh : 0 < h)
    (hi : Integrable (fun q => (X q - v) ^ 2) μ)
    (he : (∫ q, (X q - v) ^ 2 ∂μ) ≤ h ^ 2 / 64) :
    μ.real {q | h < |X q - v|} ≤ 1/64 :=
  failure_probability_le_of_mean_square μ X v h (1/64) hh hi (by nlinarith [he])

lemma median_bad_count (k : ℕ) (x : Fin (2 * k + 1) → ℝ) (v h : ℝ)
    (hbad : h < |sortedMedian k x - v|) :
    k + 1 ≤ (Finset.univ.filter (fun i => h < |x i - v|)).card := by
  rcases lt_abs.mp hbad with hh | hl
  · have hmed : v + h < sortedMedian k x := by linarith
    rw [sortedMedian_eq_sampleOrderStatistic] at hmed
    have hc := (lt_sampleOrderStatistic_iff (k + 1) (by omega) (by simp; omega) x (v + h)).1 hmed
    apply hc.trans
    apply Finset.card_le_card
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hx := (Finset.mem_filter.mp hi).2
    exact lt_abs.mpr (Or.inl (by linarith))
  · have hmed : sortedMedian k x < v - h := by linarith
    have hc : (Finset.univ.filter (fun i => v - h ≤ x i)).card < k + 1 := by
      apply not_le.mp
      intro hcount
      exact (not_le.mpr hmed) ((le_sortedMedian_iff k x (v - h)).2 hcount)
    have htotal := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin (2 * k + 1) => v - h ≤ x i)
    simp only [Finset.card_univ, Fintype.card_fin, not_le] at htotal
    have hlow : k + 1 ≤ (Finset.univ.filter (fun i => x i < v - h)).card := by omega
    apply hlow.trans
    apply Finset.card_le_card
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hx := (Finset.mem_filter.mp hi).2
    exact lt_abs.mpr (Or.inr (by linarith))

lemma iid_bad_intersection_probability {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Set Ω) (S : Finset ι) :
    (Measure.pi (fun _ : ι => μ)).real {q | ∀ i ∈ S, q i ∈ B} = (μ.real B) ^ S.card := by
  have hset : {q : ι → Ω | ∀ i ∈ S, q i ∈ B} =
      Set.pi Set.univ (fun i => if i ∈ S then B else Set.univ) := by
    ext q
    constructor
    · intro hq i _
      by_cases hi : i ∈ S
      · simpa only [hi, ↓reduceIte] using hq i hi
      · simp [hi]
    · intro hq i hi
      have hqi := hq i (Set.mem_univ _)
      simpa only [hi, ↓reduceIte] using hqi
  have hp : (Measure.pi (fun _ : ι => μ)) {q | ∀ i ∈ S, q i ∈ B} = (μ B) ^ S.card := by
    rw [hset, Measure.pi_pi]
    simp [apply_ite, Finset.prod_ite_mem]
  change ENNReal.toReal ((Measure.pi (fun _ : ι => μ)) {q | ∀ i ∈ S, q i ∈ B}) = _
  rw [hp, ENNReal.toReal_pow]
  rfl

lemma iid_bad_count_probability {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Set Ω) (r : ℕ) (δ : ℝ)
    (hB : μ.real B ≤ δ) :
    (Measure.pi (fun _ : ι => μ)).real
      {q | r ≤ (Finset.univ.filter (fun i => q i ∈ B)).card} ≤
      (((Finset.univ : Finset ι).powersetCard r).card : ℝ) * δ ^ r := by
  let A : Finset (Finset ι) := Finset.univ.powersetCard r
  let E : Finset ι → Set (ι → Ω) := fun S => {q | ∀ i ∈ S, q i ∈ B}
  have hsub : {q | r ≤ (Finset.univ.filter (fun i => q i ∈ B)).card} ⊆ ⋃ S ∈ A, E S := by
    intro q hq
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hq
    refine Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    · intro i hi
      exact (Finset.mem_filter.mp (hS hi)).2
  calc
    _ ≤ (Measure.pi (fun _ : ι => μ)).real (⋃ S ∈ A, E S) :=
      measureReal_mono hsub (measure_ne_top (Measure.pi (fun _ : ι => μ)) _)
    _ ≤ ∑ S ∈ A, (Measure.pi (fun _ : ι => μ)).real (E S) := measureReal_biUnion_finset_le A E
    _ ≤ ∑ _S ∈ A, δ ^ r := by
      apply Finset.sum_le_sum
      intro S hS
      have hcard := (Finset.mem_powersetCard.mp hS).2
      rw [iid_bad_intersection_probability, hcard]
      exact pow_le_pow_left₀ measureReal_nonneg hB r
    _ = _ := by simp [A, nsmul_eq_mul]

lemma median_union_factor_le (k : ℕ) :
    (2 : ℝ) ^ (2 * k + 1) * (1 / 64 : ℝ) ^ (k + 1) ≤ (1 / 4 : ℝ) ^ (2 * k + 1) := by
  have he : (2 : ℝ) ^ (2 * k + 1) * (1 / 64 : ℝ) ^ (k + 1) =
      (1 / 32 : ℝ) * (1 / 16 : ℝ) ^ k := by
    rw [pow_add, pow_mul, pow_succ]
    norm_num
    calc
      _ = (1 / 32 : ℝ) * ((4 : ℝ) ^ k * (1 / 64 : ℝ) ^ k) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  have hr : (1 / 4 : ℝ) ^ (2 * k + 1) = (1 / 4 : ℝ) * (1 / 16 : ℝ) ^ k := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  rw [he, hr]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16) k]

noncomputable def medianEstimate {Ω : Type*} (k : ℕ) (X : Ω → ℝ) (q : Fin (2 * k + 1) → Ω) : ℝ :=
  (countedMedian k (fun i => X (q i))).1

/-- Exponential confidence from literal independent copies of the experiment. -/
theorem medianEstimate_failure_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (v h : ℝ) (k : ℕ)
    (hX : μ.real {q | h < |X q - v|} ≤ 1/64) :
    (Measure.pi (fun _ : Fin (2 * k + 1) => μ)).real
      {q | h < |medianEstimate k X q - v|} ≤ (1 / 4 : ℝ) ^ (2 * k + 1) := by
  let B : Set Ω := {q | h < |X q - v|}
  have hsub : {q | h < |medianEstimate k X q - v|} ⊆
      {q | k + 1 ≤ (Finset.univ.filter (fun i => q i ∈ B)).card} := by
    intro q hq
    apply median_bad_count k (fun i => X (q i)) v h
    simpa only [Set.mem_setOf_eq, medianEstimate, countedMedian_value] using hq
  have hcard : (Finset.univ.powersetCard (k + 1) : Finset (Finset (Fin (2 * k + 1)))).card ≤
      2 ^ (2 * k + 1) := by
    calc
      _ ≤ Finset.univ.powerset.card := Finset.card_le_card (fun S hS =>
        Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1)
      _ = _ := by simp
  have hcardR : ((Finset.univ.powersetCard (k + 1) : Finset (Finset (Fin (2 * k + 1)))).card : ℝ) ≤
      (2 : ℝ) ^ (2 * k + 1) := by exact_mod_cast hcard
  calc
    _ ≤ (Measure.pi (fun _ : Fin (2 * k + 1) => μ)).real
        {q | k + 1 ≤ (Finset.univ.filter (fun i => q i ∈ B)).card} := measureReal_mono hsub
    _ ≤ ((Finset.univ.powersetCard (k + 1) : Finset (Finset (Fin (2 * k + 1)))).card : ℝ) *
        (1 / 64 : ℝ) ^ (k + 1) := iid_bad_count_probability μ B (k + 1) (1/64) hX
    _ ≤ (2 : ℝ) ^ (2 * k + 1) * (1 / 64 : ℝ) ^ (k + 1) :=
      mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ ≤ _ := median_union_factor_le k

lemma measurable_sortedMedian (k : ℕ) : Measurable (sortedMedian (α := ℝ) k) := by
  have hEq : sortedMedian (α := ℝ) k =
      sampleOrderStatistic (ι := Fin (2 * k + 1)) (k + 1) (by omega) (by simp; omega) := by
    funext x
    exact sortedMedian_eq_sampleOrderStatistic k x
  rw [hEq]
  exact measurable_sampleOrderStatistic (k + 1) (by omega) (by simp; omega)

lemma measurable_medianEstimate {Ω : Type*} [MeasurableSpace Ω] (k : ℕ)
    (X : Ω → ℝ) (hX : Measurable X) : Measurable (medianEstimate k X) := by
  have hEq : medianEstimate k X = fun q => sortedMedian k (fun i => X (q i)) := by
    funext q
    exact countedMedian_value k _
  rw [hEq]
  exact (measurable_sortedMedian k).comp
    (measurable_pi_iff.mpr (fun i => hX.comp (measurable_pi_apply i)))

theorem medianEstimate_of_mean_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (v h : ℝ) (hh : 0 < h) (k : ℕ)
    (hi : Integrable (fun q => (X q - v) ^ 2) μ)
    (he : (∫ q, (X q - v) ^ 2 ∂μ) ≤ h ^ 2 / 64) :
    Measurable (medianEstimate k X) ∧
      (Measure.pi (fun _ : Fin (2 * k + 1) => μ)).real
        {q | h < |medianEstimate k X q - v|} ≤ (1 / 4 : ℝ) ^ (2 * k + 1) :=
  ⟨measurable_medianEstimate k X hX, medianEstimate_failure_probability μ X v h k
    (failure_probability_le_one_sixtyFourth μ X v h hh hi he)⟩

/-- Confidence selection uses arithmetic search, followed by exactly the
specified number of calls and a counted sorting median. -/
def confidenceMedianCopies {K α Seed : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [LinearOrder α] (p : K) (H : ∃ n : ℕ, (1 / 4 : K) ^ n ≤ p)
    (call : Seed → α × ℕ) (seed : Fin (confidenceCopyCount p H) → Seed) : MedianCopiesResult α :=
  let level := countedConfidenceLevel p H
  let median := countedMedianCopies level.1 call seed
  { value := median.value, work := level.2 + median.work, copies := median.copies }

lemma confidenceMedianCopies_value {K α Seed : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [LinearOrder α] (p : K) (H : ∃ n : ℕ, (1 / 4 : K) ^ n ≤ p)
    (call : Seed → α × ℕ) (seed : Fin (confidenceCopyCount p H) → Seed) :
    (confidenceMedianCopies p H call seed).value =
      sortedMedian (countedConfidenceLevel p H).1 (fun i => (call (seed i)).1) :=
  countedMedianCopies_value _ _ _

lemma confidenceMedianCopies_copies {K α Seed : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [LinearOrder α] (p : K) (H : ∃ n : ℕ, (1 / 4 : K) ^ n ≤ p)
    (call : Seed → α × ℕ) (seed : Fin (confidenceCopyCount p H) → Seed) :
    (confidenceMedianCopies p H call seed).copies = confidenceCopyCount p H :=
  countedMedianCopies_copies _ _ _

lemma confidenceMedianCopies_work {K α Seed : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [LinearOrder α] (p : K) (H : ∃ n : ℕ, (1 / 4 : K) ^ n ≤ p)
    (call : Seed → α × ℕ) (seed : Fin (confidenceCopyCount p H) → Seed) (W : ℕ)
    (hW : ∀ s, (call s).2 ≤ W) :
    (confidenceMedianCopies p H call seed).work ≤
      confidenceCopyCount p H * W + 10 * (confidenceCopyCount p H + 1) ^ 2 := by
  have hs := countedConfidenceLevel_work_le_copyCount p H
  have hm := countedMedianCopies_work (countedConfidenceLevel p H).1 call seed W hW
  change (countedConfidenceLevel p H).2 +
    (countedMedianCopies (countedConfidenceLevel p H).1 call seed).work ≤ _
  change (countedMedianCopies (countedConfidenceLevel p H).1 call seed).work ≤
    confidenceCopyCount p H * W + 8 * (confidenceCopyCount p H + 1) ^ 2 at hm
  nlinarith

/-- The actual confidence-amplified procedure is measurable, has failure at
most `p`, makes a logarithmic number of iid calls, and has a hard work bound. -/
theorem confidenceMedianCopies_correct {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (call : Ω → ℝ × ℕ)
    (hcall : Measurable (fun q => (call q).1)) (v h p : ℝ) (hh : 0 < h)
    (hp : 0 < p) (hp1 : p < 1) (H : ∃ n : ℕ, (1 / 4 : ℝ) ^ n ≤ p)
    (hi : Integrable (fun q => ((call q).1 - v) ^ 2) μ)
    (he : (∫ q, ((call q).1 - v) ^ 2 ∂μ) ≤ h ^ 2 / 64)
    (W : ℕ) (hW : ∀ q, (call q).2 ≤ W) :
    Measurable (fun q => (confidenceMedianCopies p H call q).value) ∧
      (Measure.pi (fun _ : Fin (confidenceCopyCount p H) => μ)).real
        {q | h < |(confidenceMedianCopies p H call q).value - v|} ≤ p ∧
      (confidenceCopyCount p H : ℝ) < 2 * (Real.log (1 / p) / Real.log 4) + 3 ∧
      ∀ q, (confidenceMedianCopies p H call q).copies = confidenceCopyCount p H ∧
        (confidenceMedianCopies p H call q).work ≤
          confidenceCopyCount p H * W + 10 * (confidenceCopyCount p H + 1) ^ 2 := by
  have hEq : (fun q => (confidenceMedianCopies p H call q).value) =
      medianEstimate (countedConfidenceLevel p H).1 (fun q => (call q).1) := by
    funext q
    rw [confidenceMedianCopies_value, medianEstimate, countedMedian_value]
  have hm := medianEstimate_of_mean_square μ (fun q => (call q).1) hcall v h hh
    (countedConfidenceLevel p H).1 hi he
  refine ⟨?_, ?_, confidenceCopyCount_log_bound hp hp1 H, ?_⟩
  · rw [hEq]
    exact hm.1
  · have htail : (Measure.pi (fun _ : Fin (confidenceCopyCount p H) => μ)).real
        {q | h < |(confidenceMedianCopies p H call q).value - v|} ≤
          (1 / 4 : ℝ) ^ confidenceCopyCount p H := by
      unfold confidenceCopyCount
      simpa only [confidenceMedianCopies_value, medianEstimate, countedMedian_value] using hm.2
    exact htail.trans (confidenceCopyCount_failure p H)
  · intro q
    exact ⟨confidenceMedianCopies_copies p H call q, confidenceMedianCopies_work p H call q W hW⟩

end ProphetSecretary.Probability
