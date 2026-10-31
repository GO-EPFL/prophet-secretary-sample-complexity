import ProphetSecretary.Statistics.MixedDataSelectedRegionRates
import ProphetSecretary.Statistics.MixedDataSelectedTinyLoss
import ProphetSecretary.Statistics.DataSelectedCandidateRate

/-!
# Complete actual mixed per-candidate expected rate

The original explicit scalar-interval constant works for every fixed declared
known-label set. Both loss directions combine actual entrance moments, true
regional time bounds, the countable nonnegative cover and actual tiny pending
means. No residual moment, independence or loss-domination premise remains.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.mixedDataSelectedClockLossDirection_large_rate (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi x : ℝ}
    (hZ : Measurable Z) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hZrange : ∀ y, Z y ∈ Icc lo hi) (hxk : 1/(k : ℝ) ≤ x) (reverse : Bool) :
    (∫ q, ∫ t, mixedDataSelectedClockLossDirection P known Z reverse x q t ∂Instance.uniformClock
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      (empiricalNearRegretConstant lo hi + empiricalFarRegretConstant lo hi +
        empiricalEarlyRegretConstant lo hi) * (1+P.totalFirstMoment)*x/(k : ℝ) := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  let a := 4*(hi/lo)*x
  let L := fun qt : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) =>
    mixedDataSelectedClockLossDirection P known Z reverse x qt.1 qt.2
  let N := clockRegionLoss P Z hi a (x/2) true L
  let G := clockRegionLoss P Z hi a (x/2) false L
  let E := fun j : ℕ => clockRegionLoss P (fun _ => hi) hi (2*((2 : ℝ)^j*a)) ((2 : ℝ)^j*a) true L
  have hP := P.integrable_maximum_of_bounded hbound
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  have ha : 0 < a := by dsimp [a]; positivity
  have hLI : Integrable L (μ.prod Instance.uniformClock) := by
    have h := P.integrable_mixedDataSelectedClockLoss_pair known hbound hZ
      (fun y => ⟨(hlo.trans_le (hZrange y).1).le,(hZrange y).2⟩) x
    cases reverse
    · exact h.1
    · exact h.2
  have hN := P.mixedDataSelectedClockLoss_near_expectation known hbound hZ hlo hlohi hZrange hxk reverse
  have hG := P.mixedDataSelectedClockLoss_far_expectation known hbound hZ hlo hlohi hZrange hxk reverse
  have hE := P.mixedDataSelectedClockLoss_early_expectation_sum known hbound hZ hlo hlohi hZrange hxk reverse
  have h0 (q) (t) : 0 ≤ L (q,t) := mixedDataSelectedClockLossDirection_nonnegative P known Z reverse x q t
  have hN0 : ∀ᵐ q ∂μ, 0 ≤ N q := Filter.Eventually.of_forall (clockRegionLoss_nonnegative P Z _ _ _ _ h0)
  have hG0 : ∀ᵐ q ∂μ, 0 ≤ G q := Filter.Eventually.of_forall (clockRegionLoss_nonnegative P Z _ _ _ _ h0)
  have hE0 (j) : ∀ᵐ q ∂μ, 0 ≤ E j q :=
    Filter.Eventually.of_forall (clockRegionLoss_nonnegative P (fun _ => hi) _ _ _ _ h0)
  have hcover : ∀ᵐ q ∂μ, ENNReal.ofReal (∫ t, L (q,t) ∂Instance.uniformClock) ≤
      ENNReal.ofReal (N q) + ENNReal.ofReal (G q) + ∑' j, ENNReal.ofReal (E j q) := by
    filter_upwards [hLI.prod_right_ae] with q hq
    exact P.clockRegionLoss_ofReal_cover hP hhi.le ha q hq (h0 q)
  have hc := ProphetSecretary.Analysis.integral_le_add_add_tsum_of_ofReal_cover μ
    hLI.integral_prod_left hN.1 hG.1 hE.1
    (Filter.Eventually.of_forall fun q => integral_nonneg (h0 q)) hN0 hG0 hE0 hE.2.1 hcover
  have hFar0 := (empirical_regional_constants_nonnegative hlo hlohi).2.2.1
  have hS := P.totalFirstMoment_nonnegative
  have hfar : empiricalFarRegretConstant lo hi*x/(k : ℝ) ≤
      empiricalFarRegretConstant lo hi*(1+P.totalFirstMoment)*x/(k : ℝ) := by
    apply div_le_div_of_nonneg_right _ hk.le
    nlinarith only [mul_nonneg (mul_nonneg hFar0 hS) hx.le]
  exact hc.trans ((add_le_add (add_le_add hN.2 (hG.2.trans hfar)) hE.2.2).trans_eq (by ring))

/-- The complete inverse-linear local estimate, including x=0. -/
theorem Instance.mixedDataSelectedClockLossDirection_rate (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi x : ℝ}
    (hZ : Measurable Z) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hZrange : ∀ y, Z y ∈ Icc lo hi) (hx : 0 ≤ x) (reverse : Bool) :
    (∫ q, ∫ t, mixedDataSelectedClockLossDirection P known Z reverse x q t ∂Instance.uniformClock
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalCandidateRegretConstant lo hi * (1+P.totalFirstMoment)*x/(k : ℝ) := by
  have hC := empirical_regional_constants_nonnegative hlo hlohi
  have hfac : 0 ≤ (1+P.totalFirstMoment)*x/(k : ℝ) := by
    have hS := P.totalFirstMoment_nonnegative
    positivity
  by_cases htiny : x ≤ 1/(k : ℝ)
  · have h := P.mixedDataSelectedClockLoss_pair_tiny_rate known hbound hZ hlo hlohi hZrange hx htiny
    have hb : (∫ q, ∫ t, mixedDataSelectedClockLossDirection P known Z reverse x q t ∂Instance.uniformClock
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
        empiricalTinyRegretConstant lo hi * (1+P.totalFirstMoment)*x/(k : ℝ) := by
      cases reverse
      · exact h.1
      · exact h.2
    apply hb.trans
    have hK : empiricalTinyRegretConstant lo hi ≤ empiricalCandidateRegretConstant lo hi := by
      unfold empiricalCandidateRegretConstant
      linarith only [hC.2.1,hC.2.2.1,hC.2.2.2]
    convert mul_le_mul_of_nonneg_right hK hfac using 1 <;> ring
  · have h := P.mixedDataSelectedClockLossDirection_large_rate known hbound hZ hlo hlohi hZrange (le_of_not_ge htiny) reverse
    apply h.trans
    have hK : empiricalNearRegretConstant lo hi + empiricalFarRegretConstant lo hi +
        empiricalEarlyRegretConstant lo hi ≤ empiricalCandidateRegretConstant lo hi := by
      unfold empiricalCandidateRegretConstant
      linarith only [hC.1]
    convert mul_le_mul_of_nonneg_right hK hfac using 1 <;> ring

end ProphetSecretary.Model
