import ProphetSecretary.Limiting.LabeledBandState

/-!
# Residual rarity removes the finite Poisson comparison error

At a fixed cutoff above reserve, the total tail count is uniformly bounded.
The squared residual probabilities are at most rarity times this count.
The explicit comparison constants are independent of finite instance size,
and the retained-prefix limit follows the original-sequence limit.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal BigOperators
namespace ProphetSecretary.Limiting

theorem LabeledBandConvergence.poisson_band_error_two_limits {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ))
    (b W : ℝ≥0) (hb : (B.terminal : ℝ)<b) (hbH : b≤B.cap) :
    ∀ ε>(0 : ℝ), ∀ᶠ N in atTop, ∀ᶠ m in atTop,
      (∀ w c : ℝ, 0≤w → w≤W → 0≤c →
        |Model.optimalTerminalScalarValue (P m) b w c-
          (labeledBandState (P m) N B.cap b hbH (hCap m)).optimalScalarValue w c|<ε) ∧
      |(P m).expectedTerminalMaximum b-
        (labeledBandState (P m) N B.cap b hbH (hCap m)).expectedMaximum|<ε := by
  obtain ⟨K,hK,hTail⟩ := h.above_reserve b hb
  let A := (Real.pi/2)*(W : ℝ)*(B.cap : ℝ)
  have hA : 0≤A := by dsimp only [A]; positivity
  intro ε hε
  let r := min 1 (ε/(2*(A+(B.cap : ℝ)+1)))
  have hr : 0<r := lt_min zero_lt_one (div_pos hε (by positivity))
  have hr1 : r≤1 := min_le_left _ _
  have hScale : (A+(B.cap : ℝ)+1)*r≤ε/2 := by
    have h := (le_div_iff₀ (by positivity : 0<2*(A+(B.cap : ℝ)+1))).mp
      (show r≤ε/(2*(A+(B.cap : ℝ)+1)) from min_le_right _ _)
    nlinarith only [h]
  let δ := r^2/(K+1)
  have hδ : 0<δ := div_pos (sq_pos_of_pos hr) (by positivity)
  have hδK : δ*K≤r^2 := by
    have he : δ*(K+1)=r^2 := div_mul_cancel₀ _ (by positivity)
    nlinarith only [he,hδ]
  obtain ⟨N₀,hRare⟩ := h.rare b hb δ hδ
  filter_upwards [eventually_ge_atTop N₀] with N hN
  filter_upwards [hRare] with m hm
  have hSquare : (∑ i : Fin (sizes m), ((labeledRemainder (P m) N).law i).real (Ioi (b : ℝ))^2)≤r^2 := by
    have h := labeledRemainder_tail_square_sum_le (P m) N b.property
      (fun j hj => (hm j (hN.trans hj)).le)
    exact h.trans ((mul_le_mul_of_nonneg_left (hTail m) hδ.le).trans hδK)
  have hSqrt : Real.sqrt (∑ i : Fin (sizes m), ((labeledRemainder (P m) N).law i).real (Ioi (b : ℝ))^2)≤r := by
    simpa only [Real.sqrt_sq_eq_abs,abs_of_pos hr] using Real.sqrt_le_sqrt hSquare
  constructor
  · intro w c hw hwW hc
    have hCausal := labeledBandState_value_comparison (P m) N B.cap b hbH (hCap m) hw hc
    have hCoef : (Real.pi/2)*w*(B.cap : ℝ)≤A := by dsimp only [A]; gcongr
    have hBound : (Real.pi/2)*w*(B.cap : ℝ)*
        Real.sqrt (∑ i : Fin (sizes m), ((labeledRemainder (P m) N).law i).real (Ioi (b : ℝ))^2)≤A*r :=
      mul_le_mul hCoef hSqrt (Real.sqrt_nonneg _) hA
    exact hCausal.trans_lt (hBound.trans_lt (by nlinarith only [hScale,hr,B.cap.property,hε]))
  · have hM := labeledBandState_benchmark_comparison (P m) N B.cap b hbH (hCap m)
    rw [abs_of_nonneg hM.1]
    have hBound := mul_le_mul_of_nonneg_left hSquare B.cap.property
    have hr2 : r^2≤r := by nlinarith only [hr,hr1]
    have hHr := mul_le_mul_of_nonneg_left hr2 B.cap.property
    have hStep : (B.cap : ℝ)*r^2≤ε/2 := hHr.trans
      ((mul_le_mul_of_nonneg_right (show (B.cap : ℝ)≤A+(B.cap : ℝ)+1 by linarith only [hA]) hr.le).trans hScale)
    exact hM.2.trans_lt (hBound.trans_lt (hStep.trans_lt (by linarith only [hε])))

end ProphetSecretary.Limiting
