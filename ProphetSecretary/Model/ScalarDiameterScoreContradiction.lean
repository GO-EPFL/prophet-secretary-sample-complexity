import ProphetSecretary.Model.SmoothEnvelopeDuration

/-!
# A nonzero duration response rules out divergent diameter ratios

The policies are fixed midpoint optimizers of the actual finite instances.
A common information bound gives one smooth-envelope constant. The proof
never divides by the scalar gap, so zero-gap counterexamples are included.
Paper correspondence: `updual:derivative` and `updual:elimination` followed
by the contradiction step in `updual:modulus`.
-/

open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability

theorem scalarDiameter_countersequence_impossible_of_durationScore_limit
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H S0 δ I0 : ℝ}
    (hH : 0≤H) (hS0 : 0≤S0) (hδ : 0<δ) (hI0 : 0≤I0)
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H) (hS : ∀ m, (P m).totalFirstMoment≤S0)
    (a b : ℕ → ℝ) (hA : ∀ m, a m∈Icc δ (1-δ)) (hB : ∀ m, b m∈Icc δ (1-δ))
    (π : ∀ m, RandomizedPolicy (sizes m))
    (hOpt : ∀ m, (π m).scalarObjective (P m) ((a m+b m)/2) (1-(a m+b m)/2)=
      optimalScalarValue (P m) ((a m+b m)/2) (1-(a m+b m)/2))
    (h : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (h m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |h m i x|≤1)
    (hm : ∀ m i, ∫ x, h m i x ∂(P m).law i=0)
    (hInfo : ∀ m, information (P m).law (h m)≤I0)
    (hRatio : ∀ m : ℕ, ((m : ℝ)+1)*(normalizedScalarGap (P m) (a m)+normalizedScalarGap (P m) (b m))<(b m-a m)^2)
    {d : ℝ} (hd : d≠0)
    (hResponse : Tendsto (fun m => (π m).expectedDurationScore (P m) (h m)) atTop (𝓝 d)) : False := by
  let q := fun m => normalizedScalarGap (P m) (a m)+normalizedScalarGap (P m) (b m)
  let D := |smoothEnvelopeDurationConstant H S0 δ I0|
  let b0 := |d|/2
  have hb0 : 0<b0 := div_pos (abs_pos.mpr hd) (by norm_num)
  have hb02 : 0<b0^2 := sq_pos_of_pos hb0
  obtain ⟨m0,hm0⟩ := Metric.tendsto_atTop.mp hResponse.abs b0 hb0
  obtain ⟨m1,hm1⟩ := exists_nat_gt (D^2/b0^2)
  let m := max m0 m1
  have hLower : b0≤|(π m).expectedDurationScore (P m) (h m)| := by
    have hDist := hm0 m (le_max_left _ _)
    rw [Real.dist_eq] at hDist
    have hLeft := (abs_lt.mp hDist).1
    dsimp only [b0] at hLeft ⊢
    linarith only [hLeft]
  have hCast : (m1 : ℝ)≤m := by exact_mod_cast (le_max_right m0 m1)
  have hThreshold : D^2≤((m : ℝ)+1)*b0^2 :=
    (div_le_iff₀ hb02).mp (hm1.le.trans (by linarith only [hCast]))
  have hUnitA : a m∈Icc (0 : ℝ) 1 := ⟨hδ.le.trans (hA m).1,by linarith only [(hA m).2,hδ]⟩
  have hUnitB : b m∈Icc (0 : ℝ) 1 := ⟨hδ.le.trans (hB m).1,by linarith only [(hB m).2,hδ]⟩
  have hPI := (P m).integrable_maximum_of_bounded (hcap m)
  have hQ0 : 0≤q m := add_nonneg
    (normalizedScalarGap_nonnegative (P m) hPI hUnitA)
    (normalizedScalarGap_nonnegative (P m) hPI hUnitB)
  have hBound := (π m).midpoint_durationScore_separation_bound (P m) hH hS0 hδ hI0
    (hcap m) (hS m) (hA m) (hB m) (hOpt m) (h m) (hh m) (hb m) (hm m) (hInfo m)
  have hD : 0≤D := abs_nonneg _
  have hSB : |b m-a m| * b0≤D*Real.sqrt (q m) := by
    calc
      _ ≤ |b m-a m| * |(π m).expectedDurationScore (P m) (h m)| :=
        mul_le_mul_of_nonneg_left hLower (abs_nonneg _)
      _ ≤ smoothEnvelopeDurationConstant H S0 δ I0*Real.sqrt (q m) := hBound
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
  have hSquare : (|b m-a m| * b0)^2≤(D*Real.sqrt (q m))^2 :=
    (sq_le_sq₀ (mul_nonneg (abs_nonneg _) hb0.le) (mul_nonneg hD (Real.sqrt_nonneg _))).mpr hSB
  rw [mul_pow,mul_pow,sq_abs,Real.sq_sqrt hQ0] at hSquare
  have hThresholdQ := mul_le_mul_of_nonneg_right hThreshold hQ0
  have hStrict := mul_lt_mul_of_pos_right (hRatio m) hb02
  change ((m : ℝ)+1)*q m*b0^2<(b m-a m)^2*b0^2 at hStrict
  nlinarith only [hSquare,hThresholdQ,hStrict]

end ProphetSecretary.Model
