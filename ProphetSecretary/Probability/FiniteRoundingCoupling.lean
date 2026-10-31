import ProphetSecretary.Probability.FiniteProbabilityRounding
import Mathlib.Probability.HasLaw

/-!
# An explicit diagonal/reset coupling of rounded finite probabilities

The first coordinate has the original law and the second the rounded law.
Every pair is diagonal or resets the second coordinate to the distinguished
zero element. The mismatch probability is exactly the mass moved to zero.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Probability

variable {Θ : Type*} [Fintype Θ] [DecidableEq Θ]

noncomputable def roundingPairProbability (p : Θ → ℝ) (N : ℕ) (z : Θ) (ab : Θ × Θ) : ℝ :=
  if ab.1=z then (if ab.2=z then p z else 0) else
    (if ab.2=ab.1 then roundedProbability p N z ab.1 else 0) +
    (if ab.2=z then p ab.1-roundedProbability p N z ab.1 else 0)

lemma roundingPair_row_sum (p : Θ → ℝ) (N : ℕ) (z a : Θ) :
    (∑ b, roundingPairProbability p N z (a,b)) = p a := by
  by_cases ha : a=z
  · subst a
    simp [roundingPairProbability]
  · simp [roundingPairProbability,ha,Finset.sum_add_distrib]

lemma roundingPair_column_sum (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) (N : ℕ) (z b : Θ) :
    (∑ a, roundingPairProbability p N z (a,b)) = roundedProbability p N z b := by
  by_cases hb : b=z
  · subst b
    have hSplit := Finset.sum_erase_add (s := Finset.univ) (f := fun a => roundingPairProbability p N z (a,z))
      (Finset.mem_univ z)
    have hEach (a : Θ) (ha : a∈Finset.univ.erase z) :
        roundingPairProbability p N z (a,z) = p a-floorProbability N (p a) := by
      have h := (Finset.mem_erase.mp ha).1
      simp [roundingPairProbability,h,Ne.symm h,roundedProbability_nonzero p N z a h]
    have hSum : (∑ a∈Finset.univ.erase z, roundingPairProbability p N z (a,z)) = roundingLoss p N z :=
      Finset.sum_congr rfl hEach
    rw [hSum,show roundingPairProbability p N z (z,z)=p z by simp [roundingPairProbability]] at hSplit
    have h := roundedProbability_zero_loss p hp N z
    linarith only [h,hSplit]
  · have hEach (a : Θ) : roundingPairProbability p N z (a,b) =
        if a=b then roundedProbability p N z b else 0 := by
      by_cases ha : a=z
      · subst a
        simp [roundingPairProbability,hb,Ne.symm hb]
      · by_cases hab : a=b
        · subst a
          simp [roundingPairProbability,hb]
        · simp [roundingPairProbability,ha,hb,hab,Ne.symm hab]
    simp_rw [hEach]
    simp

lemma roundingPair_simplex (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) {N : ℕ} (hN : 0 < N) (z : Θ) :
    roundingPairProbability p N z∈stdSimplex ℝ (Θ × Θ) := by
  refine ⟨?_,?_⟩
  · rintro ⟨a,b⟩
    by_cases ha : a=z
    · subst a
      by_cases hb : b=z
      · subst b
        simpa [roundingPairProbability] using hp.1 z
      · simp [roundingPairProbability,hb]
    · have hQ : 0 ≤ roundedProbability p N z a := (roundedProbability_simplex p hp hN z).1 a
      have hLoss : 0 ≤ p a-roundedProbability p N z a := by
        rw [roundedProbability_nonzero p N z a ha]
        exact sub_nonneg.mpr (floorProbability_le hN (hp.1 a))
      simp only [roundingPairProbability,if_neg ha]
      apply add_nonneg
      · split_ifs <;> positivity
      · split_ifs <;> positivity
  · rw [Fintype.sum_prod_type]
    simp_rw [roundingPair_row_sum]
    exact hp.2

variable [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

noncomputable def roundingCoupling (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) (N : ℕ) (hN : 0 < N) (z : Θ) :
    Measure (Θ × Θ) := finiteSimplexLaw (roundingPairProbability p N z) (roundingPair_simplex p hp hN z)

instance roundingCoupling_probability (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) (N : ℕ) (hN : 0 < N) (z : Θ) :
    IsProbabilityMeasure (roundingCoupling p hp N hN z) := by unfold roundingCoupling;infer_instance

lemma roundingCoupling_integral_fst (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ)
    (N : ℕ) (hN : 0<N) (z : Θ) (f : Θ → ℝ) :
    (∫ ab, f ab.1 ∂roundingCoupling p hp N hN z) = ∫ a, f a ∂finiteSimplexLaw p hp := by
  rw [roundingCoupling, integral_finiteSimplexLaw, integral_finiteSimplexLaw,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ b, roundingPairProbability p N z (a,b)*f a) = _
  rw [← Finset.sum_mul, roundingPair_row_sum]

lemma roundingCoupling_integral_snd (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ)
    (N : ℕ) (hN : 0<N) (z : Θ) (f : Θ → ℝ) :
    (∫ ab, f ab.2 ∂roundingCoupling p hp N hN z) =
      ∫ a, f a ∂finiteSimplexLaw (roundedProbability p N z) (roundedProbability_simplex p hp hN z) := by
  rw [roundingCoupling, integral_finiteSimplexLaw, integral_finiteSimplexLaw,
    Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  change (∑ a, roundingPairProbability p N z (a,b)*f b) = _
  rw [← Finset.sum_mul, roundingPair_column_sum p hp]

omit [DecidableEq Θ] in
private lemma finiteMeasure_eq_of_integrals {μ ν : Measure Θ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : Θ → ℝ, (∫ a, f a ∂μ) = ∫ a, f a ∂ν) : μ=ν := by
  apply Measure.ext_of_singleton
  intro a
  apply (measureReal_eq_measureReal_iff).mp
  have he := h (({a} : Set Θ).indicator (fun _ => (1 : ℝ)))
  simpa only [integral_indicator_const _ (measurableSet_singleton a), smul_eq_mul, mul_one] using he

lemma roundingCoupling_fst (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ)
    (N : ℕ) (hN : 0<N) (z : Θ) :
    MeasurePreserving Prod.fst (roundingCoupling p hp N hN z) (finiteSimplexLaw p hp) := by
  refine ⟨measurable_fst, ?_⟩
  letI : IsProbabilityMeasure ((roundingCoupling p hp N hN z).map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  apply finiteMeasure_eq_of_integrals
  intro f
  rw [integral_map measurable_fst.aemeasurable (measurable_of_finite f).aestronglyMeasurable]
  exact roundingCoupling_integral_fst p hp N hN z f

lemma roundingCoupling_snd (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ)
    (N : ℕ) (hN : 0<N) (z : Θ) :
    MeasurePreserving Prod.snd (roundingCoupling p hp N hN z)
      (finiteSimplexLaw (roundedProbability p N z) (roundedProbability_simplex p hp hN z)) := by
  refine ⟨measurable_snd, ?_⟩
  letI : IsProbabilityMeasure ((roundingCoupling p hp N hN z).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  apply finiteMeasure_eq_of_integrals
  intro f
  rw [integral_map measurable_snd.aemeasurable (measurable_of_finite f).aestronglyMeasurable]
  exact roundingCoupling_integral_snd p hp N hN z f

omit [MeasurableSpace Θ] [MeasurableSingletonClass Θ] in
lemma roundingPair_off_diagonal_row (p : Θ → ℝ) (N : ℕ) (z a : Θ) :
    (∑ b, if a≠b then roundingPairProbability p N z (a,b) else 0) =
      if a=z then 0 else p a-roundedProbability p N z a := by
  by_cases ha : a=z
  · subst a
    rw [if_pos rfl]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : b=z
    · subst b
      simp
    · simp [roundingPairProbability,hb,Ne.symm hb]
  · have he (b : Θ) : (if a≠b then roundingPairProbability p N z (a,b) else 0) =
        if b=z then p a-roundedProbability p N z a else 0 := by
      by_cases hab : a=b
      · subst b
        simp [ha]
      · simp [hab,roundingPairProbability,ha,Ne.symm hab]
    simp_rw [he]
    simp [ha]

omit [MeasurableSpace Θ] [MeasurableSingletonClass Θ] in
lemma roundingPair_mismatch_sum (p : Θ → ℝ) (N : ℕ) (z : Θ) :
    (∑ ab, if ab.1≠ab.2 then roundingPairProbability p N z ab else 0) = roundingLoss p N z := by
  rw [Fintype.sum_prod_type]
  simp_rw [roundingPair_off_diagonal_row]
  have he := Finset.sum_erase_add (s:=Finset.univ)
    (f:=fun a => if a=z then 0 else p a-roundedProbability p N z a) (Finset.mem_univ z)
  simp only [ite_true] at he
  rw [← he, add_zero]
  apply Finset.sum_congr rfl
  intro a ha
  rw [if_neg (Finset.mem_erase.mp ha).1,
    roundedProbability_nonzero p N z a (Finset.mem_erase.mp ha).1]

lemma roundingCoupling_mismatch (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ)
    (N : ℕ) (hN : 0<N) (z : Θ) :
    (roundingCoupling p hp N hN z).real {ab | ab.1≠ab.2} = roundingLoss p N z := by
  have h := integral_finiteSimplexLaw (roundingPairProbability p N z)
    (roundingPair_simplex p hp hN z) (({ab : Θ × Θ | ab.1≠ab.2} : Set (Θ × Θ)).indicator (fun _ => (1 : ℝ)))
  have hI := integral_indicator_const (μ:=roundingCoupling p hp N hN z) (1 : ℝ)
    (Set.toFinite {ab : Θ × Θ | ab.1≠ab.2}).measurableSet
  rw [smul_eq_mul,mul_one] at hI
  rw [← hI]
  change (∫ ab, {ab | ab.1≠ab.2}.indicator (fun _ => (1 : ℝ)) ab
    ∂finiteSimplexLaw (roundingPairProbability p N z) (roundingPair_simplex p hp hN z)) = _
  rw [h]
  simp only [Set.indicator_apply,Set.mem_setOf_eq,mul_ite,mul_one,mul_zero]
  exact roundingPair_mismatch_sum p N z

omit [MeasurableSpace Θ] [MeasurableSingletonClass Θ] in
lemma roundedProbability_l1 (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ)
    (N : ℕ) (hN : 0<N) (z : Θ) :
    (∑ a, |p a-roundedProbability p N z a|) = 2*roundingLoss p N z := by
  have hSplit := Finset.sum_erase_add (s:=Finset.univ)
    (f:=fun a => |p a-roundedProbability p N z a|) (Finset.mem_univ z)
  have hOther : (∑ a∈Finset.univ.erase z, |p a-roundedProbability p N z a|) = roundingLoss p N z := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [roundedProbability_nonzero p N z a (Finset.mem_erase.mp ha).1,
      abs_of_nonneg (sub_nonneg.mpr (floorProbability_le hN (hp.1 a)))]
  rw [hOther] at hSplit
  have hz : |p z-roundedProbability p N z z| = roundingLoss p N z := by
    rw [abs_sub_comm, ← roundedProbability_zero_loss p hp N z]
    exact abs_of_nonneg (by rw [roundedProbability_zero_loss p hp N z]; exact roundingLoss_nonnegative p hp hN z)
  rw [hz] at hSplit
  linarith only [hSplit]

lemma roundingCoupling_diagonal_or_zero (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ)
    (N : ℕ) (hN : 0<N) (z : Θ) :
    ∀ᵐ ab ∂roundingCoupling p hp N hN z, ab.2=ab.1 ∨ ab.2=z := by
  rw [ae_iff_of_countable]
  rintro ⟨a,b⟩ hMass
  by_contra hBad
  have hb : b≠a ∧ b≠z := not_or.mp hBad
  have hZero : (roundingCoupling p hp N hN z).real {(a,b)}=0 := by
    rw [roundingCoupling,finiteSimplexLaw_real_singleton]
    by_cases ha : a=z <;> simp [roundingPairProbability,ha,hb.1,hb.2]
  exact hMass ((measureReal_eq_zero_iff).mp hZero)

lemma roundingCoupling_value_le (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ)
    (N : ℕ) (hN : 0<N) (z : Θ) (v : Θ → ℝ) (hv : ∀ a, 0≤v a) (hz : v z=0) :
    ∀ᵐ ab ∂roundingCoupling p hp N hN z, v ab.2 ≤ v ab.1 := by
  filter_upwards [roundingCoupling_diagonal_or_zero p hp N hN z] with ab hab
  rcases hab with h|h
  · rw [h]
  · rw [h,hz]
    exact hv _

lemma roundingCoupling_expectation_error (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ)
    (N : ℕ) (hN : 0<N) (z : Θ) (f : Θ → ℝ) {D : ℝ}
    (hOsc : ∀ a b, |f a-f b|≤D) :
    |(∫ a, f a ∂finiteSimplexLaw p hp)-
      ∫ a, f a ∂finiteSimplexLaw (roundedProbability p N z) (roundedProbability_simplex p hp hN z)| ≤
      D*roundingLoss p N z := by
  rw [← roundingCoupling_integral_fst p hp N hN z f, ← roundingCoupling_integral_snd p hp N hN z f,
    ← integral_sub (Integrable.of_finite) (Integrable.of_finite)]
  calc
    _ ≤ ∫ ab, |f ab.1-f ab.2| ∂roundingCoupling p hp N hN z := abs_integral_le_integral_abs
    _ ≤ ∫ ab, {ab : Θ × Θ | ab.1≠ab.2}.indicator (fun _ => D) ab ∂roundingCoupling p hp N hN z := by
      apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
      intro ab
      by_cases h : ab.1=ab.2
      · simp [h]
      · simpa [Set.indicator_apply,h] using hOsc ab.1 ab.2
    _ = D*roundingLoss p N z := by
      rw [integral_indicator_const _ (Set.toFinite _).measurableSet,smul_eq_mul,
        roundingCoupling_mismatch,mul_comm]

end ProphetSecretary.Probability
