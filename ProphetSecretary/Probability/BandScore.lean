import ProphetSecretary.Probability.LikelihoodTilt

/-!
# Finite scores for a positive band and a zero atom

This is the finite score in `con:finite-scores`. Counts refer to the complete offer
vector, including offers arriving after selection. No optimizer or limiting-score
convergence is asserted here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Probability

noncomputable def bandScore (μ : Measure ℝ) (B : Set ℝ) (x : ℝ) : ℝ :=
  B.indicator (fun _ => 1) x - (μ.real B / μ.real {0}) * ({0} : Set ℝ).indicator (fun _ => 1) x

lemma measurable_bandScore (μ : Measure ℝ) {B : Set ℝ} (hB : MeasurableSet B) : Measurable (bandScore μ B) :=
  (measurable_const.indicator hB).sub (measurable_const.mul (measurable_const.indicator (measurableSet_singleton 0)))

lemma band_mass_le_zero_mass (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0}) : μ.real B ≤ μ.real {0} := by
  have hsub : B ⊆ ({0} : Set ℝ)ᶜ := by intro x hx hx0; exact hB0 (by simpa only [mem_singleton_iff.mp hx0] using hx)
  have hp := measureReal_mono (μ := μ) hsub
  rw [measureReal_compl (measurableSet_singleton 0), probReal_univ] at hp
  linarith

lemma bandScore_of_mem (μ : Measure ℝ) {B : Set ℝ} (hB0 : (0 : ℝ) ∉ B) {x : ℝ} (hx : x ∈ B) :
    bandScore μ B x = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hB0 hx
  simp [bandScore, Set.indicator_of_mem hx, hx0]

lemma bandScore_at_zero (μ : Measure ℝ) {B : Set ℝ} (hB0 : (0 : ℝ) ∉ B) :
    bandScore μ B 0 = -(μ.real B / μ.real {0}) := by simp [bandScore, hB0]

lemma bandScore_abs_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0}) (x : ℝ) : |bandScore μ B x| ≤ 1 := by
  have hqpos : 0 < μ.real {0} := by linarith
  have hpq := band_mass_le_zero_mass μ hB0 hq
  have hratio0 : 0 ≤ μ.real B / μ.real {0} := div_nonneg measureReal_nonneg measureReal_nonneg
  have hratio1 : μ.real B / μ.real {0} ≤ 1 := (div_le_one hqpos).mpr hpq
  by_cases hxB : x ∈ B
  · rw [bandScore_of_mem μ hB0 hxB]
    norm_num
  · by_cases hx0 : x = 0
    · subst x
      rw [bandScore_at_zero μ hB0, abs_neg, abs_of_nonneg hratio0]
      exact hratio1
    · simp [bandScore, Set.indicator_of_notMem hxB, hx0]

lemma bandScore_mean (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB : MeasurableSet B) (hq : (1 / 2 : ℝ) ≤ μ.real {0}) : (∫ x, bandScore μ B x ∂μ) = 0 := by
  have hqpos : 0 < μ.real {0} := by linarith
  have hiB : Integrable (B.indicator (fun _ : ℝ => (1 : ℝ))) μ := (integrable_const 1).indicator hB
  have hi0 : Integrable (({0} : Set ℝ).indicator (fun _ : ℝ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator (measurableSet_singleton 0)
  unfold bandScore
  rw [integral_sub hiB (hi0.const_mul _), integral_const_mul,
    integral_indicator_const 1 hB, integral_indicator_const 1 (measurableSet_singleton 0)]
  simp only [smul_eq_mul, mul_one]
  field_simp
  ring

lemma bandScore_sq_pointwise (μ : Measure ℝ) {B : Set ℝ} (hB0 : (0 : ℝ) ∉ B) (x : ℝ) :
    bandScore μ B x ^ 2 = B.indicator (fun _ => (1 : ℝ)) x +
      (μ.real B / μ.real {0}) ^ 2 * ({0} : Set ℝ).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx0 : x = 0
  · subst x; simp [bandScore, hB0]
  · by_cases hxB : x ∈ B
    · simp [bandScore, Set.indicator_of_mem hxB, hx0]
    · simp [bandScore, Set.indicator_of_notMem hxB, hx0]

lemma bandScore_secondMoment (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB : MeasurableSet B) (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0}) :
    (∫ x, bandScore μ B x ^ 2 ∂μ) = μ.real B + (μ.real B) ^ 2 / μ.real {0} := by
  have hqpos : 0 < μ.real {0} := by linarith
  have hiB : Integrable (B.indicator (fun _ : ℝ => (1 : ℝ))) μ := (integrable_const 1).indicator hB
  have hi0 : Integrable (({0} : Set ℝ).indicator (fun _ : ℝ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator (measurableSet_singleton 0)
  simp_rw [bandScore_sq_pointwise μ hB0]
  rw [integral_add hiB (hi0.const_mul _), integral_const_mul,
    integral_indicator_const 1 hB, integral_indicator_const 1 (measurableSet_singleton 0)]
  simp only [smul_eq_mul, mul_one]
  field_simp

lemma bandScore_secondMoment_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB : MeasurableSet B) (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0}) :
    (∫ x, bandScore μ B x ^ 2 ∂μ) ≤ 2 * μ.real B := by
  rw [bandScore_secondMoment μ hB hB0 hq]
  have hqpos : 0 < μ.real {0} := by linarith
  have hpq := band_mass_le_zero_mass μ hB0 hq
  have hratio : μ.real B / μ.real {0} ≤ 1 := (div_le_one hqpos).mpr hpq
  have h := mul_le_mul_of_nonneg_left hratio (measureReal_nonneg (μ := μ) (s := B))
  nlinarith [show (μ.real B) ^ 2 / μ.real {0} = μ.real B * (μ.real B / μ.real {0}) by ring]

lemma bandScore_tilt_band_mass (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB : MeasurableSet B) (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0})
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    (tiltLaw μ (bandScore μ B) θ).real B = (1 + θ) * μ.real B := by
  have hh := measurable_bandScore μ hB
  have hb : ∀ᵐ x ∂μ, |bandScore μ B x| ≤ 1 := Filter.Eventually.of_forall (bandScore_abs_le_one μ hB0 hq)
  haveI := tiltLaw_probability hh hb (bandScore_mean μ hB hq) hθ
  have hInt := integral_indicator_const (μ := tiltLaw μ (bandScore μ B) θ) (1 : ℝ) hB
  simp only [smul_eq_mul, mul_one] at hInt
  rw [← hInt, integral_tiltLaw hh (tiltFactor_ae_nonnegative hb hθ)]
  calc
    _ = ∫ x, (1 + θ) * B.indicator (fun _ : ℝ => (1 : ℝ)) x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        by_cases hx : x ∈ B
        · simp only [tiltFactor, Set.indicator_of_mem hx, bandScore_of_mem μ hB0 hx, mul_one]
        · rw [Set.indicator_of_notMem hx]
          simp
    _ = _ := by rw [integral_const_mul, integral_indicator_const 1 hB]; simp

lemma bandScore_tilt_zero_mass (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB : MeasurableSet B) (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0})
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    (tiltLaw μ (bandScore μ B) θ).real {0} = μ.real {0} - θ * μ.real B := by
  have hh := measurable_bandScore μ hB
  have hb : ∀ᵐ x ∂μ, |bandScore μ B x| ≤ 1 := Filter.Eventually.of_forall (bandScore_abs_le_one μ hB0 hq)
  haveI := tiltLaw_probability hh hb (bandScore_mean μ hB hq) hθ
  have hInt := integral_indicator_const (μ := tiltLaw μ (bandScore μ B) θ) (1 : ℝ) (measurableSet_singleton 0)
  simp only [smul_eq_mul, mul_one] at hInt
  rw [← hInt, integral_tiltLaw hh (tiltFactor_ae_nonnegative hb hθ)]
  calc
    _ = ∫ x, (1 - θ * (μ.real B / μ.real {0})) * ({0} : Set ℝ).indicator (fun _ : ℝ => (1 : ℝ)) x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        by_cases hx : x = 0
        · subst x
          simp [tiltFactor, bandScore_at_zero μ hB0, sub_eq_add_neg]
        · simp [Set.indicator, hx]
    _ = _ := by
      rw [integral_const_mul, integral_indicator_const 1 (measurableSet_singleton 0)]
      simp only [smul_eq_mul, mul_one]
      have hqpos : 0 < μ.real {0} := by linarith
      field_simp

/-- Real-valued count of occurrences in a measurable set on the complete vector. -/
noncomputable def countIn {N : ℕ} (B : Set ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i, B.indicator (fun _ => (1 : ℝ)) (x i)

lemma completeBandScore_eq_counts (μ : Measure ℝ) (B : Set ℝ) (N : ℕ) (x : Fin N → ℝ) :
    completeScore (fun _ : Fin N => bandScore μ B) x = countIn B x - (μ.real B / μ.real {0}) * countIn {0} x := by
  simp only [completeScore, bandScore, countIn, Finset.sum_sub_distrib, Finset.mul_sum]

lemma completeBandScore_secondMoment_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB : MeasurableSet B) (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0})
    (N : ℕ) :
    (∫ x : Fin N → ℝ, completeScore (fun _ : Fin N => bandScore μ B) x ^ 2 ∂Measure.pi (fun _ : Fin N => μ)) ≤
      2 * N * μ.real B := by
  rw [completeScore_secondMoment (fun _ : Fin N => μ) (fun _ => bandScore μ B)
    (fun _ => measurable_bandScore μ hB)
    (fun _ => Filter.Eventually.of_forall (bandScore_abs_le_one μ hB0 hq))
    (fun _ => bandScore_mean μ hB hq)]
  unfold information
  calc
    _ ≤ ∑ _i : Fin N, 2 * μ.real B := Finset.sum_le_sum fun i _ => bandScore_secondMoment_le μ hB hB0 hq
    _ = _ := by simp [nsmul_eq_mul, mul_assoc, mul_comm]

lemma completeBandScore_variance_le_intensity (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB : MeasurableSet B) (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0})
    (N : ℕ) (hN : 0 < N) {intensity : ℝ} (hp : μ.real B = intensity / (N : ℝ)) :
    (∫ x : Fin N → ℝ, completeScore (fun _ : Fin N => bandScore μ B) x ^ 2 ∂Measure.pi (fun _ : Fin N => μ)) ≤ 2 * intensity := by
  have h := completeBandScore_secondMoment_le μ hB hB0 hq N
  rw [hp] at h
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  convert h using 1
  field_simp

/-- The finite complete score differs from the centered band count by a vanishing
L² error. The law and the two counts are all finite; no Poisson convergence is assumed. -/
lemma completeBandScore_centeredCount_L2 (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (_hB : MeasurableSet B) (_hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0})
    (N : ℕ) (hN : 0 < N) {intensity : ℝ} (hp : μ.real B = intensity / (N : ℝ)) :
    (∫ x : Fin N → ℝ, (completeScore (fun _ : Fin N => bandScore μ B) x - (countIn B x - intensity)) ^ 2
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ 2 * intensity ^ 2 / N := by
  let p := μ.real B
  let q := μ.real {0}
  have hqpos : 0 < q := by dsimp [q]; linarith
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hNp : (N : ℝ) * p = intensity := by dsimp [p]; rw [hp]; field_simp
  let s : ℝ → ℝ := centeredIndicator ({0} : Set ℝ) q
  have hsM : Measurable s := centeredIndicator_measurable (measurableSet_singleton 0) q
  have hsB : ∀ᵐ x ∂μ, |s x| ≤ 1 := Filter.Eventually.of_forall fun x =>
    centeredIndicator_abs_le_one {0} measureReal_nonneg measureReal_le_one x
  have hs0 : (∫ x, s x ∂μ) = 0 := centeredIndicator_mean (measurableSet_singleton 0)
  have hsRep (x : Fin N → ℝ) : completeScore (fun _ : Fin N => s) x = countIn {0} x - N * q := by
    simp only [completeScore, s, centeredIndicator, countIn, Set.indicator, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rfl
  have hs2 : (∫ x : Fin N → ℝ, completeScore (fun _ : Fin N => s) x ^ 2 ∂Measure.pi (fun _ : Fin N => μ)) =
      N * (q - q ^ 2) := by
    rw [completeScore_secondMoment (fun _ : Fin N => μ) (fun _ => s) (fun _ => hsM) (fun _ => hsB) (fun _ => hs0)]
    simp only [information, s, q, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [centeredIndicator_secondMoment (μ := μ) (measurableSet_singleton 0)]
  have hgap (x : Fin N → ℝ) :
      completeScore (fun _ : Fin N => bandScore μ B) x - (countIn B x - intensity) =
        -(p / q) * completeScore (fun _ : Fin N => s) x := by
    rw [completeBandScore_eq_counts, hsRep, ← hNp]
    dsimp [p, q]
    field_simp
    ring
  simp_rw [hgap]
  simp only [mul_pow, neg_sq]
  rw [integral_const_mul, hs2]
  calc
    _ ≤ (p / q) ^ 2 * ((N : ℝ) * q) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sub_le_self q (sq_nonneg q)) (Nat.cast_nonneg N)) (sq_nonneg _)
    _ = (N : ℝ) * p ^ 2 / q := by field_simp
    _ ≤ 2 * (N : ℝ) * p ^ 2 := by
      have hrecip : 1 / q ≤ 2 := (div_le_iff₀ hqpos).mpr (by dsimp [q]; linarith)
      have h := mul_le_mul_of_nonneg_left hrecip (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg p))
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, one_mul, mul_one] using h
    _ = 2 * intensity ^ 2 / N := by rw [← hNp]; field_simp

lemma bandScore_integrable_pow (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB : MeasurableSet B) (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0}) (k : ℕ) :
    Integrable (fun x => bandScore μ B x ^ k) μ :=
  integrable_pow_of_bound (measurable_bandScore μ hB) zero_le_one
    (Filter.Eventually.of_forall (bandScore_abs_le_one μ hB0 hq)) k

lemma completeBandScore_integrable_pow (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB : MeasurableSet B) (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0}) (N k : ℕ) :
    Integrable (fun x : Fin N → ℝ => completeScore (fun _ : Fin N => bandScore μ B) x ^ k)
      (Measure.pi (fun _ : Fin N => μ)) :=
  completeScore_integrable_pow (fun _ : Fin N => μ) (fun _ => bandScore μ B)
    (fun _ => measurable_bandScore μ hB)
    (fun _ => Filter.Eventually.of_forall (bandScore_abs_le_one μ hB0 hq)) k

lemma completeBandScore_mean (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB : MeasurableSet B) (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0}) (N : ℕ) :
    (∫ x : Fin N → ℝ, completeScore (fun _ : Fin N => bandScore μ B) x ∂Measure.pi (fun _ : Fin N => μ)) = 0 :=
  completeScore_mean (fun _ : Fin N => μ) (fun _ => bandScore μ B)
    (fun _ => measurable_bandScore μ hB)
    (fun _ => Filter.Eventually.of_forall (bandScore_abs_le_one μ hB0 hq)) (fun _ => bandScore_mean μ hB hq)

lemma completeBandScore_secondMoment (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB : MeasurableSet B) (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0}) (N : ℕ) :
    (∫ x : Fin N → ℝ, completeScore (fun _ : Fin N => bandScore μ B) x ^ 2 ∂Measure.pi (fun _ : Fin N => μ)) =
      N * (μ.real B + (μ.real B) ^ 2 / μ.real {0}) := by
  rw [completeScore_secondMoment (fun _ : Fin N => μ) (fun _ => bandScore μ B)
    (fun _ => measurable_bandScore μ hB)
    (fun _ => Filter.Eventually.of_forall (bandScore_abs_le_one μ hB0 hq)) (fun _ => bandScore_mean μ hB hq)]
  simp only [information, bandScore_secondMoment μ hB hB0 hq, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma completeBandScore_abs_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0}) (N : ℕ) (x : Fin N → ℝ) :
    |completeScore (fun _ : Fin N => bandScore μ B) x| ≤ N := by
  calc
    _ ≤ ∑ i : Fin N, |bandScore μ B (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => bandScore_abs_le_one μ hB0 hq (x i)
    _ = _ := by simp

lemma countIn_abs_le (B : Set ℝ) (N : ℕ) (x : Fin N → ℝ) : |countIn B x| ≤ N := by
  calc
    _ ≤ ∑ i : Fin N, |B.indicator (fun _ : ℝ => (1 : ℝ)) (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      unfold Set.indicator
      split_ifs <;> norm_num
    _ = _ := by simp

lemma completeBandScore_centeredCount_integrable_sq (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB : MeasurableSet B) (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0})
    (N : ℕ) (intensity : ℝ) :
    Integrable (fun x : Fin N → ℝ =>
      (completeScore (fun _ : Fin N => bandScore μ B) x - (countIn B x - intensity)) ^ 2)
      (Measure.pi (fun _ : Fin N => μ)) := by
  have hcountM : Measurable (@countIn N B) := Finset.measurable_sum _
    (fun i _ => (measurable_const.indicator hB).comp (measurable_pi_apply i))
  have hscoreM := measurable_completeScore (fun _ : Fin N => measurable_bandScore μ hB)
  have hb : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      |completeScore (fun _ : Fin N => bandScore μ B) x - (countIn B x - intensity)| ≤ 2 * N + |intensity| := by
    exact Filter.Eventually.of_forall fun x => by
      have h1 := abs_add_le (completeScore (fun _ : Fin N => bandScore μ B) x) (-(countIn B x - intensity))
      have h2 := abs_add_le (countIn B x) (-intensity)
      have hz := completeBandScore_abs_le μ hB0 hq N x
      have hc := countIn_abs_le B N x
      simp only [abs_neg, ← sub_eq_add_neg] at h1 h2
      linarith
  have hGapM : Measurable (fun x : Fin N → ℝ => completeScore (fun _ : Fin N => bandScore μ B) x - (countIn B x - intensity)) :=
    hscoreM.sub (hcountM.sub_const intensity)
  exact integrable_pow_of_bound hGapM (by positivity) hb 2

lemma completeBandScore_centeredCount_integrable_and_L2 (μ : Measure ℝ) [IsProbabilityMeasure μ] {B : Set ℝ}
    (hB : MeasurableSet B) (hB0 : (0 : ℝ) ∉ B) (hq : (1 / 2 : ℝ) ≤ μ.real {0})
    (N : ℕ) (hN : 0 < N) {intensity : ℝ} (hp : μ.real B = intensity / (N : ℝ)) :
    Integrable (fun x : Fin N → ℝ =>
      (completeScore (fun _ : Fin N => bandScore μ B) x - (countIn B x - intensity)) ^ 2)
      (Measure.pi (fun _ : Fin N => μ)) ∧
    (∫ x : Fin N → ℝ, (completeScore (fun _ : Fin N => bandScore μ B) x - (countIn B x - intensity)) ^ 2
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ 2 * intensity ^ 2 / N :=
  ⟨completeBandScore_centeredCount_integrable_sq μ hB hB0 hq N intensity,
    completeBandScore_centeredCount_L2 μ hB hB0 hq N hN hp⟩

end ProphetSecretary.Probability
