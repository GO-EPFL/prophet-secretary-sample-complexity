import ProphetSecretary.Limiting.HybridOutcomeBounds
import ProphetSecretary.Stability.Modulus

/-!
# Uniform stability in finite-intensity hybrid families

The modulus is chosen before the retained dimension, actual finite cloud
intensity, normalized interior weights and general randomized competitor.
Only the common cap and uniform positive-level tail profile enter it. This
is the finite-intensity stability component of `lem:canonical-limit`.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
variable {n : ℕ}

theorem RandomizedHybridPolicy.expectedValueOutcomeError_le_uniform (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {H δ w c b d e L4 L2 Ld : ℝ}
    (hH : 0 ≤ H) (hCap : (B.cap : ℝ) ≤ H) (hδ : 0 < δ)
    (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w+c=1)
    (hb : 0 < b) (hbsmall : b < δ/2) (hd : 0 ≤ d) (he0 : 0 < e) (he : e ≤ δ*b/4)
    (hL4 : B.tailCount (b/4) ≤ L4) (hL2 : B.tailCount (b/2) ≤ L2) (hLd : B.tailCount d ≤ Ld) :
    π.expectedValueOutcomeError B w c ≤
      (H+1)*((B.optimalScalarValue w c-π.scalarObjective B w c)/e+
        Model.uniformStabilityBandConstant H δ b L4 L2*e)+2*b/δ+d+(2*H*b/δ)*Ld := by
  have hw : 0 < w := hδ.trans_le hwδ
  have hc : 0 < c := hδ.trans_le hcδ
  have hw1 : w ≤ 1 := by linarith
  have hc1 : c ≤ 1 := by linarith
  let window := 2*w*b/c
  have hw0 : 0 ≤ window := by dsimp only [window]; positivity
  have hδw : δ*w ≤ c := by
    have h := mul_le_mul_of_nonneg_left hw1 hδ.le
    nlinarith
  have hwBound : window ≤ 2*b/δ := by
    apply (div_le_div_iff₀ hc hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδw (show 0 ≤ 2*b by positivity)]
  have hwWindow : window ≤ 1 := hwBound.trans ((div_lt_one hδ).mpr (by linarith)).le
  have heActual : e ≤ w*b/4 :=
    he.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hwδ hb.le) (by norm_num))
  have hRaw := π.expectedValueOutcomeError_le_window B ha hH hCap hw hc hb hd he0 heActual hwWindow
  have hBand := B.positiveValueBand_probability ha π.seedLaw hH hCap hw hc hb hL4 hL2 he0.le heActual
  have hL40 : 0 ≤ L4 := (B.tailCount_nonnegative _).trans hL4
  have hL20 : 0 ≤ L2 := (B.tailCount_nonnegative _).trans hL2
  have hCoeff : 2*L2/(c*Model.positiveBandDuration H w c b L4) ≤
      Model.uniformStabilityBandConstant H δ b L4 L2 := by
    calc
      _ ≤ 2*L2/(c*Model.positiveBandDuration H w c b L4)+4/(w*b) :=
        le_add_of_nonneg_right (by positivity)
      _ ≤ _ := Model.stabilityBandConstant_le_uniform hH hδ hb hL40 hL20 hwδ hcδ hw1 hc1
  have hBand' := hBand.trans (mul_le_mul_of_nonneg_right hCoeff he0.le)
  have hBandTerm := mul_le_mul_of_nonneg_left
    (add_le_add_left hBand' ((B.optimalScalarValue w c-π.scalarObjective B w c)/e))
    (show 0 ≤ H+1 by linarith)
  have hLd0 : 0 ≤ Ld := (B.tailCount_nonnegative d).trans hLd
  have hTail0 := mul_le_mul_of_nonneg_left hLd (mul_nonneg hH hw0)
  have hTail1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwBound hH) hLd0
  change H*window*B.tailCount d ≤ H*window*Ld at hTail0
  change H*window*Ld ≤ H*(2*b/δ)*Ld at hTail1
  have hCoef : H*(2*b/δ)*Ld = (2*H*b/δ)*Ld := by ring
  rw [hCoef] at hTail1
  change π.expectedValueOutcomeError B w c ≤ window+
    (H+1)*((B.optimalScalarValue w c-π.scalarObjective B w c)/e+
      (B.law π.seedLaw).real (B.positiveValueBand w c b e))+d+H*window*B.tailCount d at hRaw
  nlinarith only [hRaw,hBandTerm,hwBound,hTail0,hTail1]

structure HybridStabilityComparison {α : Type*} (n : α → ℕ) (δ : ℝ) where
  instanceIndex : α
  rewardWeight : ℝ
  durationWeight : ℝ
  reward_interior : δ ≤ rewardWeight
  duration_interior : δ ≤ durationWeight
  normalized : rewardWeight+durationWeight=1
  competitor : RandomizedHybridPolicy (n instanceIndex)

/-- A single modulus works for all actual count-hidden hybrid competitors.
There is no bound on total intensity, retained dimension or seed space. -/
theorem finite_hybrid_outcome_stability_with_profile {α : Type*} (n : α → ℕ)
    (B : ∀ a, FiniteIntensityHybridInstance (n a)) {H δ : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ)
    (ha : ∀ a, (B a).terminal=0) (hCap : ∀ a, ((B a).cap : ℝ) ≤ H)
    (L : ℝ → ℝ) (hL : ∀ d, 0 < d → 0 ≤ L d)
    (hTail : ∀ a d, 0 < d → (B a).tailCount d ≤ L d) :
    ∃ ω : ℝ → ℝ, (∀ t, 0 ≤ ω t ∧ ω t ≤ H+1) ∧ Monotone ω ∧ ω 0=0 ∧
      Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      (∀ a w c, δ ≤ w → δ ≤ c → w+c=1 → ∀ π : RandomizedHybridPolicy (n a),
        π.expectedValueOutcomeError (B a) w c ≤
          ω ((B a).optimalScalarValue w c-π.scalarObjective (B a) w c)) ∧
      (∀ t < 0, ω t=0) := by
  let E : HybridStabilityComparison n δ → ℝ := fun i =>
    i.competitor.expectedValueOutcomeError (B i.instanceIndex) i.rewardWeight i.durationWeight
  let r : HybridStabilityComparison n δ → ℝ := fun i =>
    (B i.instanceIndex).optimalScalarValue i.rewardWeight i.durationWeight-
      i.competitor.scalarObjective (B i.instanceIndex) i.rewardWeight i.durationWeight
  let K : ℝ → ℝ := fun b => Model.uniformStabilityBandConstant H δ b (L (b/4)) (L (b/2))
  have hE : ∀ i, E i ∈ Icc (0 : ℝ) (H+1) := by
    intro i
    exact ⟨i.competitor.expectedValueOutcomeError_nonnegative _ _ _,
      i.competitor.expectedValueOutcomeError_le_bound _ hH (hCap i.instanceIndex)
        (hδ.le.trans i.reward_interior) (hδ.le.trans i.duration_interior)⟩
  have hr : ∀ i, 0 ≤ r i := by
    intro i
    exact sub_nonneg.mpr ((B i.instanceIndex).scalarObjective_le_value i.competitor _ _)
  have hK : ∀ b, 0 < b → 0 ≤ K b := by
    intro b hb
    exact (Model.uniformStabilityBandConstant_positive hH hδ hb
      (hL (b/4) (by positivity)) (hL (b/2) (by positivity))).le
  have hEstimate : ∀ i b, b ∈ Ioo (0 : ℝ) (δ/2) → ∀ d, 0 < d → ∀ e,
      e ∈ Ioc (0 : ℝ) (δ*b/4) →
      E i ≤ (H+1)*(r i/e+K b*e)+2*b/δ+d+(2*H*b/δ)*L d := by
    intro i b hb d hd e he
    have hb0 : 0 < b := hb.1
    exact i.competitor.expectedValueOutcomeError_le_uniform _ (ha i.instanceIndex) hH (hCap i.instanceIndex)
      hδ i.reward_interior i.duration_interior i.normalized hb.1 hb.2 hd.le he.1 he.2
      (hTail i.instanceIndex (b/4) (by positivity))
      (hTail i.instanceIndex (b/2) (by positivity)) (hTail i.instanceIndex d hd)
  obtain ⟨ω,hω,hMono,hZero,hLim,hError,hNeg⟩ :=
    ProphetSecretary.Stability.exists_radiusModulus_of_finite_estimate E r hH hδ hE hr L K hL hK hEstimate
  refine ⟨ω,hω,hMono,hZero,hLim,?_,hNeg⟩
  intro a w c hw hc hSum π
  exact hError ⟨a,w,c,hw,hc,hSum,π⟩

end ProphetSecretary.Limiting
