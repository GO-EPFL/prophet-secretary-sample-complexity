import ProphetSecretary.Model.Independence
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Fourth moments of independent centered bounded sums

The constants in these bounds are explicit and independent of the number of variables.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integrable_pow_of_bound {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂μ, |f ω| ≤ C) (k : ℕ) : Integrable (fun ω => f ω ^ k) μ := by
  apply Integrable.of_bound (hf.pow_const k).aestronglyMeasurable (C ^ k)
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hω k

lemma integrable_finsetSum_pow_of_bound (s : Finset ι) (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hb : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1) (k : ℕ) :
    Integrable (fun ω => (∑ i ∈ s, X i ω) ^ k) μ := by
  apply integrable_pow_of_bound (by fun_prop) (Nat.cast_nonneg s.card) _ k
  have hae : ∀ᵐ ω ∂μ, ∀ i ∈ s, |X i ω| ≤ 1 := by
    exact (Filter.eventually_all_finset s).mpr (fun i _ => hb i)
  filter_upwards [hae] with ω hω
  calc
    |∑ i ∈ s, X i ω| ≤ ∑ i ∈ s, |X i ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, (1 : ℝ) := Finset.sum_le_sum fun i hi => hω i hi
    _ = s.card := by simp

omit [IsProbabilityMeasure μ] in
lemma _root_.ProbabilityTheory.IndepFun.integral_pow_mul_pow {X Y : Ω → ℝ} (h : IndepFun X Y μ)
    (hX : Measurable X) (hY : Measurable Y) (a b : ℕ) :
    (∫ ω, X ω ^ a * Y ω ^ b ∂μ) = (∫ ω, X ω ^ a ∂μ) * ∫ ω, Y ω ^ b ∂μ := by
  exact (h.comp (measurable_id.pow_const a) (measurable_id.pow_const b)).integral_fun_mul_eq_mul_integral
    (hX.pow_const a).aestronglyMeasurable (hY.pow_const b).aestronglyMeasurable

omit [IsProbabilityMeasure μ] in
lemma _root_.ProbabilityTheory.IndepFun.integrable_pow_mul_pow {X Y : Ω → ℝ} (h : IndepFun X Y μ)
    (_hX : Measurable X) (_hY : Measurable Y) (a b : ℕ)
    (ha : Integrable (fun ω => X ω ^ a) μ) (hb : Integrable (fun ω => Y ω ^ b) μ) :
    Integrable (fun ω => X ω ^ a * Y ω ^ b) μ := by
  exact (h.comp (measurable_id.pow_const a) (measurable_id.pow_const b)).integrable_mul ha hb

omit [IsProbabilityMeasure μ] in
lemma integral_add_pow_two {X Y : Ω → ℝ} (h : IndepFun X Y μ)
    (hX : Measurable X) (hY : Measurable Y)
    (hXp : ∀ k : ℕ, Integrable (fun ω => X ω ^ k) μ)
    (hYp : ∀ k : ℕ, Integrable (fun ω => Y ω ^ k) μ)
    (hmX : ∫ ω, X ω ∂μ = 0) (hmY : ∫ ω, Y ω ∂μ = 0) :
    (∫ ω, (X ω + Y ω) ^ 2 ∂μ) = (∫ ω, X ω ^ 2 ∂μ) + ∫ ω, Y ω ^ 2 ∂μ := by
  have hXY := h.integrable_pow_mul_pow hX hY 1 1 (hXp 1) (hYp 1)
  simp only [pow_one] at hXY
  have hsum : Integrable (fun ω => X ω ^ 2 + 2 * (X ω * Y ω)) μ :=
    (hXp 2).add (hXY.const_mul 2)
  calc
    _ = ∫ ω, (X ω ^ 2 + 2 * (X ω * Y ω)) + Y ω ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by ring
    _ = _ := by
      rw [integral_add hsum (hYp 2),
        integral_add (hXp 2) (hXY.const_mul 2), integral_const_mul]
      have hm := h.integral_pow_mul_pow hX hY 1 1
      simp only [pow_one, hmX, hmY, zero_mul] at hm
      rw [hm]
      ring

omit [IsProbabilityMeasure μ] in
lemma integral_add_pow_four {X Y : Ω → ℝ} (h : IndepFun X Y μ)
    (hX : Measurable X) (hY : Measurable Y)
    (hXp : ∀ k : ℕ, Integrable (fun ω => X ω ^ k) μ)
    (hYp : ∀ k : ℕ, Integrable (fun ω => Y ω ^ k) μ)
    (hmX : ∫ ω, X ω ∂μ = 0) (hmY : ∫ ω, Y ω ∂μ = 0) :
    (∫ ω, (X ω + Y ω) ^ 4 ∂μ) = (∫ ω, X ω ^ 4 ∂μ) +
      6 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) + ∫ ω, Y ω ^ 4 ∂μ := by
  have h31 := h.integrable_pow_mul_pow hX hY 3 1 (hXp 3) (hYp 1)
  have h22 := h.integrable_pow_mul_pow hX hY 2 2 (hXp 2) (hYp 2)
  have h13 := h.integrable_pow_mul_pow hX hY 1 3 (hXp 1) (hYp 3)
  have hsum1 : Integrable (fun ω => X ω ^ 4 + 4 * (X ω ^ 3 * Y ω ^ 1)) μ :=
    (hXp 4).add (h31.const_mul 4)
  have hsum2 : Integrable (fun ω => (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω ^ 1)) + 6 * (X ω ^ 2 * Y ω ^ 2)) μ :=
    hsum1.add (h22.const_mul 6)
  have hsum3 : Integrable (fun ω => ((X ω ^ 4 + 4 * (X ω ^ 3 * Y ω ^ 1)) + 6 * (X ω ^ 2 * Y ω ^ 2)) + 4 * (X ω ^ 1 * Y ω ^ 3)) μ :=
    hsum2.add (h13.const_mul 4)
  calc
    _ = ∫ ω, (((X ω ^ 4 + 4 * (X ω ^ 3 * Y ω ^ 1)) +
        6 * (X ω ^ 2 * Y ω ^ 2)) + 4 * (X ω ^ 1 * Y ω ^ 3)) + Y ω ^ 4 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by ring
    _ = _ := by
      rw [integral_add hsum3 (hYp 4),
        integral_add hsum2 (h13.const_mul 4),
        integral_add hsum1 (h22.const_mul 6),
        integral_add (hXp 4) (h31.const_mul 4)]
      simp only [integral_const_mul, h.integral_pow_mul_pow hX hY]
      simp only [pow_one, hmX, hmY, mul_zero, zero_mul, add_zero]
      ring

lemma integral_finsetSum_centered (s : Finset ι) (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hb : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hm : ∀ i, ∫ ω, X i ω ∂μ = 0) : (∫ ω, ∑ i ∈ s, X i ω ∂μ) = 0 := by
  rw [integral_finsetSum]
  · simp only [hm, Finset.sum_const_zero]
  · intro i _
    simpa only [pow_one] using integrable_pow_of_bound (hX i) zero_le_one (hb i) 1

/-- Explicit second and fourth moment bounds, uniform in the finite index set. -/
lemma centered_sum_moment_bounds (s : Finset ι) (X : ι → Ω → ℝ) (p : ι → ℝ)
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hm : ∀ i, ∫ ω, X i ω ∂μ = 0) (hp : ∀ i, 0 ≤ p i)
    (h2 : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) ≤ p i)
    (h4 : ∀ i, (∫ ω, X i ω ^ 4 ∂μ) ≤ p i) :
    (∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ) ≤ ∑ i ∈ s, p i ∧
    (∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ) ≤ (∑ i ∈ s, p i) + 3 * (∑ i ∈ s, p i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have hsmeas : Measurable (fun ω => ∑ j ∈ s, X j ω) := by fun_prop
    have hIp := fun k => integrable_pow_of_bound (hX i) zero_le_one (hb i) k
    have hSp := fun k => integrable_finsetSum_pow_of_bound s X hX hb k
    have hIS : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) μ := by
      have h := (hInd.indepFun_finsetSum_of_notMem hX his).symm
      convert h using 1
      funext ω
      simp only [Finset.sum_apply]
    have hmS := integral_finsetSum_centered s X hX hb hm
    have he2 := integral_add_pow_two hIS (hX i) hsmeas hIp hSp (hm i) hmS
    have he4 := integral_add_pow_four hIS (hX i) hsmeas hIp hSp (hm i) hmS
    have hcross : (∫ ω, X i ω ^ 2 ∂μ) * (∫ ω, (∑ j ∈ s, X j ω) ^ 2 ∂μ) ≤
        p i * (∑ j ∈ s, p j) := by
      exact mul_le_mul (h2 i) ih.1 (integral_nonneg fun _ => sq_nonneg _) (hp i)
    simp only [Finset.sum_insert his]
    constructor
    · rw [he2]
      exact add_le_add (h2 i) ih.1
    · rw [he4]
      nlinarith [h4 i, ih.2, sq_nonneg (p i)]

lemma centered_sum_fourthMoment (s : Finset ι) (X : ι → Ω → ℝ) (p : ι → ℝ)
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hm : ∀ i, ∫ ω, X i ω ∂μ = 0) (hp : ∀ i, 0 ≤ p i)
    (h2 : ∀ i, (∫ ω, X i ω ^ 2 ∂μ) ≤ p i)
    (h4 : ∀ i, (∫ ω, X i ω ^ 4 ∂μ) ≤ p i) :
    (∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ) ≤ (∑ i ∈ s, p i) + 3 * (∑ i ∈ s, p i) ^ 2 :=
  (centered_sum_moment_bounds s X p hX hInd hb hm hp h2 h4).2

/-- A Bernoulli indicator centered at its exact event probability. -/
noncomputable def centeredIndicator (A : Set Ω) (p : ℝ) (ω : Ω) : ℝ :=
  (if ω ∈ A then 1 else 0) - p

lemma centeredIndicator_measurable {A : Set Ω} (hA : MeasurableSet A) (p : ℝ) :
    Measurable (centeredIndicator A p) := by
  unfold centeredIndicator
  exact (Measurable.ite hA measurable_const measurable_const).sub measurable_const

omit [MeasurableSpace Ω] in
lemma centeredIndicator_abs_le_one (A : Set Ω) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : Ω) :
    |centeredIndicator A p ω| ≤ 1 := by
  classical
  unfold centeredIndicator
  split_ifs
  · rw [abs_of_nonneg (sub_nonneg.mpr hp1)]
    linarith
  · simpa only [zero_sub, abs_neg, abs_of_nonneg hp0] using hp1

lemma centeredIndicator_mean {A : Set Ω} (hA : MeasurableSet A) :
    (∫ ω, centeredIndicator A (μ.real A) ω ∂μ) = 0 := by
  have hI : Integrable (fun ω : Ω => if ω ∈ A then (1 : ℝ) else 0) μ := by
    apply Integrable.of_bound (Measurable.ite hA measurable_const measurable_const).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω => by split_ifs <;> norm_num
  have he : (∫ ω : Ω, (if ω ∈ A then (1 : ℝ) else 0) ∂μ) = μ.real A := by
    simpa only [Set.indicator, Pi.one_apply] using (integral_indicator_one (μ := μ) hA)
  change (∫ ω : Ω, (if ω ∈ A then (1 : ℝ) else 0) - μ.real A ∂μ) = 0
  rw [integral_sub hI (integrable_const _), he]
  simp

lemma centeredIndicator_secondMoment {A : Set Ω} (hA : MeasurableSet A) :
    (∫ ω, centeredIndicator A (μ.real A) ω ^ 2 ∂μ) = μ.real A - (μ.real A) ^ 2 := by
  let p := μ.real A
  have hI : Integrable (fun ω : Ω => if ω ∈ A then (1 : ℝ) else 0) μ := by
    apply Integrable.of_bound (Measurable.ite hA measurable_const measurable_const).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω => by split_ifs <;> norm_num
  have he : (∫ ω : Ω, (if ω ∈ A then (1 : ℝ) else 0) ∂μ) = p := by
    simpa only [Set.indicator, Pi.one_apply] using (integral_indicator_one (μ := μ) hA)
  calc
    _ = ∫ ω : Ω, (1 - 2 * p) * (if ω ∈ A then (1 : ℝ) else 0) + p ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        unfold centeredIndicator
        dsimp only
        split_ifs <;> dsimp [p] <;> ring
    _ = p - p ^ 2 := by
      rw [integral_add (hI.const_mul _) (integrable_const _), integral_const_mul, he]
      simp only [integral_const, probReal_univ, one_smul]
      ring

lemma centeredIndicator_fourthMoment_le {A : Set Ω} (hA : MeasurableSet A) :
    (∫ ω, centeredIndicator A (μ.real A) ω ^ 4 ∂μ) ≤ μ.real A := by
  have hb := fun ω => centeredIndicator_abs_le_one A (measureReal_nonneg : 0 ≤ μ.real A) measureReal_le_one ω
  have hInt := fun k => integrable_pow_of_bound (μ := μ) (centeredIndicator_measurable hA (μ.real A))
    zero_le_one (Filter.Eventually.of_forall hb) k
  calc
    _ ≤ ∫ ω, centeredIndicator A (μ.real A) ω ^ 2 ∂μ := by
      apply integral_mono_ae (hInt 4) (hInt 2)
      exact Filter.Eventually.of_forall fun ω => by
        have hsq : centeredIndicator A (μ.real A) ω ^ 2 ≤ 1 :=
          (sq_le_one_iff_abs_le_one _).mpr (hb ω)
        have hh := mul_nonneg (sq_nonneg (centeredIndicator A (μ.real A) ω)) (sub_nonneg.mpr hsq)
        nlinarith
    _ = μ.real A - (μ.real A) ^ 2 := centeredIndicator_secondMoment hA
    _ ≤ μ.real A := sub_le_self _ (sq_nonneg _)

/-- Independent draws of a measurable event have an explicit centered fourth moment. -/
lemma iid_centeredIndicator_fourthMoment (N : ℕ) {A : Set Ω} (hA : MeasurableSet A) :
    (∫ u : Fin N → Ω, (∑ i, centeredIndicator A (μ.real A) (u i)) ^ 4
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      N * μ.real A + 3 * (N * μ.real A) ^ 2 := by
  let X : Fin N → (Fin N → Ω) → ℝ := fun i u => centeredIndicator A (μ.real A) (u i)
  have hmeas := centeredIndicator_measurable hA (μ.real A)
  have hInt (i : Fin N) (k : ℕ) :
      (∫ u : Fin N → Ω, X i u ^ k ∂Measure.pi (fun _ : Fin N => μ)) =
        ∫ ω, centeredIndicator A (μ.real A) ω ^ k ∂μ := by
    have he := integral_map (μ := Measure.pi (fun _ : Fin N => μ))
      (measurable_pi_apply i).aemeasurable (hmeas.pow_const k).aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq] at he
    exact he.symm
  have hm (i : Fin N) : (∫ u : Fin N → Ω, X i u ∂Measure.pi (fun _ : Fin N => μ)) = 0 := by
    simpa only [pow_one, centeredIndicator_mean hA] using hInt i 1
  have h := centered_sum_fourthMoment (μ := Measure.pi (fun _ : Fin N => μ)) Finset.univ X
    (fun _ => μ.real A) (fun i => hmeas.comp (measurable_pi_apply i))
    (iIndepFun_pi (fun _ => hmeas.aemeasurable))
    (fun i => Filter.Eventually.of_forall fun u =>
      centeredIndicator_abs_le_one A measureReal_nonneg measureReal_le_one (u i))
    hm (fun _ => measureReal_nonneg)
    (fun i => by rw [hInt i 2, centeredIndicator_secondMoment hA]; exact sub_le_self _ (sq_nonneg _))
    (fun i => by rw [hInt i 4]; exact centeredIndicator_fourthMoment_le hA)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

/-- Explicit fourth moment of empirical event mass, without hidden horizon constants. -/
lemma iid_empiricalEvent_fourthMoment (N : ℕ) (hN : 0 < N) {A : Set Ω} (hA : MeasurableSet A) :
    (∫ u : Fin N → Ω,
      ((∑ i, (if u i ∈ A then (1 : ℝ) else 0)) / (N : ℝ) - μ.real A) ^ 4
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      μ.real A / (N : ℝ) ^ 3 + 3 * (μ.real A) ^ 2 / (N : ℝ) ^ 2 := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have he (u : Fin N → Ω) :
      ((∑ i, (if u i ∈ A then (1 : ℝ) else 0)) / (N : ℝ) - μ.real A) ^ 4 =
        ((N : ℝ)⁻¹) ^ 4 * (∑ i, centeredIndicator A (μ.real A) (u i)) ^ 4 := by
    simp only [centeredIndicator, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [hNr]
  simp_rw [he]
  rw [integral_const_mul]
  calc
    _ ≤ ((N : ℝ)⁻¹) ^ 4 * ((N : ℝ) * μ.real A + 3 * ((N : ℝ) * μ.real A) ^ 2) :=
      mul_le_mul_of_nonneg_left (iid_centeredIndicator_fourthMoment N hA) (pow_nonneg (by positivity) _)
    _ = μ.real A / (N : ℝ) ^ 3 + 3 * (μ.real A) ^ 2 / (N : ℝ) ^ 2 := by
      field_simp [hNr]

lemma uniformClock_interval_probability {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ProphetSecretary.Model.Instance.uniformClock.real (Ioc a b) = b - a := by
  rw [ProphetSecretary.Model.Instance.uniformClock, measureReal_restrict_apply measurableSet_Ioc]
  have he : Ioc a b ∩ Icc (0 : ℝ) 1 = Ioc a b := by
    apply inter_eq_left.mpr
    intro x hx
    exact ⟨ha.trans hx.1.le, hx.2.trans hb⟩
  rw [he, Real.volume_real_Ioc_of_le hab]

/-- Counts in any uniform interval satisfy the fourth moment estimate used by the
finite empirical-CDF chaining argument. -/
lemma uniform_interval_empirical_fourthMoment (N : ℕ) (hN : 0 < N)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ u : Fin N → ℝ,
      ((∑ i, (if a < u i ∧ u i ≤ b then (1 : ℝ) else 0)) / (N : ℝ) - (b - a)) ^ 4
      ∂ProphetSecretary.Model.Instance.clocksLaw N) ≤
      (b - a) / (N : ℝ) ^ 3 + 3 * (b - a) ^ 2 / (N : ℝ) ^ 2 := by
  have h := iid_empiricalEvent_fourthMoment (μ := ProphetSecretary.Model.Instance.uniformClock) (A := Ioc a b) N hN measurableSet_Ioc
  rw [uniformClock_interval_probability ha hab hb] at h
  simpa only [ProphetSecretary.Model.Instance.clocksLaw, Set.mem_Ioc] using h

end ProphetSecretary.Probability
