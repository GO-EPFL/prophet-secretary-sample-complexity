import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Analytic assembly of a uniform stability modulus

The finite numerical estimate is an explicit hypothesis in this module. The actual
online-policy estimate is a separate theorem that must discharge it. The parameter
choice is ordered: first the tag level, then the small-offer level, then the boundary
width, and finally the regret radius. No concavity of the resulting modulus is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace ProphetSecretary.Stability

/-- The stated finite bound implies a genuinely uniform small-error estimate. Tail and
boundary profiles need only be nonnegative and finite at every positive argument. -/
theorem small_errors_of_finite_estimate {ι : Type*} (E r : ι → ℝ) {H δ : ℝ}
    (hH : 0 ≤ H) (hδ : 0 < δ) (L K : ℝ → ℝ)
    (hL : ∀ d, 0 < d → 0 ≤ L d) (hK : ∀ b, 0 < b → 0 ≤ K b)
    (hEstimate : ∀ i b, b ∈ Ioo (0 : ℝ) (δ / 2) → ∀ d, 0 < d → ∀ e,
      e ∈ Ioc (0 : ℝ) (δ * b / 4) →
      E i ≤ (H + 1) * (r i / e + K b * e) + 2 * b / δ + d + (2 * H * b / δ) * L d) :
    ∀ ε, 0 < ε → ∃ η, 0 < η ∧ ∀ i, r i ≤ η → E i ≤ ε := by
  intro ε hε
  let A := H + 1
  have hA : 0 < A := by dsimp [A]; linarith
  let d := ε / 4
  have hd : 0 < d := by dsimp [d]; positivity
  let D := 1 + H * L d
  have hD : 0 < D := by dsimp [D]; have := hL d hd; positivity
  let b := min (δ / 4) (ε * δ / (8 * D))
  have hb : 0 < b := by dsimp [b]; positivity
  have hbSmall : b ∈ Ioo (0 : ℝ) (δ / 2) := by
    refine ⟨hb, (min_le_left _ _).trans_lt ?_⟩
    linarith
  have hbCross : b * (8 * D) ≤ ε * δ :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * D)).mp (min_le_right (δ / 4) (ε * δ / (8 * D)))
  have hSmall : 2 * b / δ + (2 * H * b / δ) * L d ≤ ε / 4 := by
    have heq : 2 * b / δ + (2 * H * b / δ) * L d = (2 * b * D) / δ := by dsimp [D]; ring
    rw [heq]
    apply (div_le_iff₀ hδ).mpr
    nlinarith
  let B := 1 + K b
  have hB : 0 < B := by dsimp [B]; have := hK b hb; positivity
  let e := min (δ * b / 4) (ε / (4 * A * B))
  have he : 0 < e := by dsimp [e]; positivity
  have heSmall : e ≤ δ * b / 4 := min_le_left _ _
  have heCross : e * (4 * A * B) ≤ ε :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * A * B)).mp (min_le_right (δ * b / 4) (ε / (4 * A * B)))
  have hBoundary : A * (K b * e) ≤ ε / 4 := by
    have hKB : K b ≤ B := by dsimp [B]; linarith
    have hm := mul_le_mul_of_nonneg_left hKB (mul_nonneg hA.le he.le)
    nlinarith
  let η := ε * e / (4 * A)
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  intro i hi
  have hrCross : r i * (4 * A) ≤ ε * e := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * A)).mp hi
  have hRegret : A * (r i / e) ≤ ε / 4 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ he).mpr
    nlinarith
  have h := hEstimate i b hbSmall d hd e ⟨he, heSmall⟩
  change E i ≤ A * (r i / e + K b * e) + 2 * b / δ + d + (2 * H * b / δ) * L d at h
  dsimp [d] at h hSmall
  nlinarith

/-- Error values with regret at most the radius, with a zero sentinel. -/
def errorRadiusSet {ι : Type*} (E r : ι → ℝ) (t : ℝ) : Set ℝ :=
  {z | z = 0 ∨ ∃ i, r i ≤ t ∧ z = E i}

noncomputable def radiusModulus {ι : Type*} (E r : ι → ℝ) (t : ℝ) : ℝ :=
  sSup (errorRadiusSet E r t)

lemma errorRadiusSet_nonempty {ι : Type*} (E r : ι → ℝ) (t : ℝ) :
    (errorRadiusSet E r t).Nonempty := ⟨0, Or.inl rfl⟩

lemma errorRadiusSet_bddAbove {ι : Type*} (E r : ι → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hE : ∀ i, E i ≤ A) (t : ℝ) : BddAbove (errorRadiusSet E r t) := by
  refine ⟨A, ?_⟩
  rintro z (rfl | ⟨i, _, rfl⟩)
  · exact hA
  · exact hE i

lemma radiusModulus_nonnegative {ι : Type*} (E r : ι → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hE : ∀ i, E i ≤ A) (t : ℝ) : 0 ≤ radiusModulus E r t :=
  le_csSup (errorRadiusSet_bddAbove E r hA hE t) (Or.inl rfl)

lemma radiusModulus_le_bound {ι : Type*} (E r : ι → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hE : ∀ i, E i ≤ A) (t : ℝ) : radiusModulus E r t ≤ A := by
  apply csSup_le (errorRadiusSet_nonempty E r t)
  rintro z (rfl | ⟨i, _, rfl⟩)
  · exact hA
  · exact hE i

lemma radiusModulus_monotone {ι : Type*} (E r : ι → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hE : ∀ i, E i ≤ A) : Monotone (radiusModulus E r) := by
  intro t s hts
  apply csSup_le_csSup (errorRadiusSet_bddAbove E r hA hE s) (errorRadiusSet_nonempty E r t)
  rintro z (rfl | ⟨i, hi, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨i, hi.trans hts, rfl⟩

lemma error_le_radiusModulus {ι : Type*} (E r : ι → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hE : ∀ i, E i ≤ A) (i : ι) : E i ≤ radiusModulus E r (r i) :=
  le_csSup (errorRadiusSet_bddAbove E r hA hE _) (Or.inr ⟨i, le_rfl, rfl⟩)

lemma radiusModulus_le_of_small_errors {ι : Type*} (E r : ι → ℝ) {ε η t : ℝ}
    (hε : 0 ≤ ε) (hsmall : ∀ i, r i ≤ η → E i ≤ ε) (ht : t ≤ η) :
    radiusModulus E r t ≤ ε := by
  apply csSup_le (errorRadiusSet_nonempty E r t)
  rintro z (rfl | ⟨i, hi, rfl⟩)
  · exact hε
  · exact hsmall i (hi.trans ht)

lemma radiusModulus_zero {ι : Type*} (E r : ι → ℝ) {A : ℝ} (hA : 0 ≤ A) (hE : ∀ i, E i ≤ A)
    (hsmall : ∀ ε, 0 < ε → ∃ η, 0 < η ∧ ∀ i, r i ≤ η → E i ≤ ε) :
    radiusModulus E r 0 = 0 := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨η, hη, hηE⟩ := hsmall ε hε
    simpa only [zero_add] using radiusModulus_le_of_small_errors E r hε.le hηE hη.le
  · exact radiusModulus_nonnegative E r hA hE 0

lemma radiusModulus_negative {ι : Type*} (E r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) {t : ℝ} (ht : t < 0) :
    radiusModulus E r t = 0 := by
  have hs : errorRadiusSet E r t = {0} := by
    ext z
    constructor
    · rintro (hz | ⟨i, hi, _⟩)
      · exact hz
      · exact False.elim ((not_le.mpr ht) ((hr i).trans hi))
    · intro hz
      exact Or.inl hz
  rw [radiusModulus, hs, csSup_singleton]

/-- This construction is continuous at zero even as a function on all real radii;
its right limit is the one used for nonnegative regret. -/
lemma radiusModulus_tendsto_zero {ι : Type*} (E r : ι → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hE : ∀ i, E i ≤ A)
    (hsmall : ∀ ε, 0 < ε → ∃ η, 0 < η ∧ ∀ i, r i ≤ η → E i ≤ ε) :
    Tendsto (radiusModulus E r) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨η, hη, hηE⟩ := hsmall (ε / 2) (by positivity)
  filter_upwards [Iio_mem_nhds hη] with t ht
  have hb := radiusModulus_le_of_small_errors E r (by positivity : (0 : ℝ) ≤ ε / 2) hηE ht.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (radiusModulus_nonnegative E r hA hE t)]
  exact hb.trans_lt (by linarith)

/-- Conditional analytic assembly from the explicit numerical finite estimate.
The policy-family theorem must separately supply `hEstimate`. -/
theorem exists_radiusModulus_of_finite_estimate {ι : Type*} (E r : ι → ℝ) {H δ : ℝ}
    (hH : 0 ≤ H) (hδ : 0 < δ) (hE : ∀ i, E i ∈ Icc (0 : ℝ) (H + 1)) (hr : ∀ i, 0 ≤ r i)
    (L K : ℝ → ℝ) (hL : ∀ d, 0 < d → 0 ≤ L d) (hK : ∀ b, 0 < b → 0 ≤ K b)
    (hEstimate : ∀ i b, b ∈ Ioo (0 : ℝ) (δ / 2) → ∀ d, 0 < d → ∀ e,
      e ∈ Ioc (0 : ℝ) (δ * b / 4) →
      E i ≤ (H + 1) * (r i / e + K b * e) + 2 * b / δ + d + (2 * H * b / δ) * L d) :
    ∃ ω : ℝ → ℝ, (∀ t, 0 ≤ ω t ∧ ω t ≤ H + 1) ∧ Monotone ω ∧ ω 0 = 0 ∧
      Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧ (∀ i, E i ≤ ω (r i)) ∧ (∀ t < 0, ω t = 0) := by
  have hA : 0 ≤ H + 1 := by linarith
  have hUp := fun i => (hE i).2
  have hsmall := small_errors_of_finite_estimate E r hH hδ L K hL hK hEstimate
  refine ⟨radiusModulus E r, ?_, radiusModulus_monotone E r hA hUp,
    radiusModulus_zero E r hA hUp hsmall, ?_, error_le_radiusModulus E r hA hUp,
    fun t ht => radiusModulus_negative E r hr ht⟩
  · intro t
    exact ⟨radiusModulus_nonnegative E r hA hUp t, radiusModulus_le_bound E r hA hUp t⟩
  · exact (radiusModulus_tendsto_zero E r hA hUp hsmall).mono_left nhdsWithin_le_nhds

section ScoreBounds

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Bounded coupled outcome differences have integrable products with every L² score.
The score may depend on the complete online vector, including offers after stopping. -/
lemma score_products_integrable {score dR dT : Ω → ℝ} {H : ℝ}
    (hscore : MemLp score 2 μ) (hR : AEStronglyMeasurable dR μ) (hT : AEStronglyMeasurable dT μ)
    (hRbound : ∀ᵐ ω ∂μ, |dR ω| ≤ H) (hTbound : ∀ᵐ ω ∂μ, |dT ω| ≤ 1) :
    Integrable (fun ω => score ω * dR ω) μ ∧ Integrable (fun ω => score ω * dT ω) μ := by
  have hs : Integrable score μ := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hscore
  constructor
  · exact hs.mul_bdd hR (hRbound.mono fun ω hω => by simpa only [Real.norm_eq_abs] using hω)
  · exact hs.mul_bdd hT (hTbound.mono fun ω hω => by simpa only [Real.norm_eq_abs] using hω)

/-- A combined Cauchy--Schwarz estimate gives constant one under the sum-error bound;
this is slightly stronger than the paper's constant two. No score/outcome independence or
score boundedness is assumed. -/
theorem score_stability_bound {score dR dT : Ω → ℝ} {H I W : ℝ} (hH : 0 ≤ H)
    (hscore : MemLp score 2 μ) (hR : AEStronglyMeasurable dR μ) (hT : AEStronglyMeasurable dT μ)
    (hRbound : ∀ᵐ ω ∂μ, |dR ω| ≤ H) (hTbound : ∀ᵐ ω ∂μ, |dT ω| ≤ 1)
    (hInfo : (∫ ω, score ω ^ 2 ∂μ) ≤ I)
    (hMean : (∫ ω, (|dR ω| + |dT ω|) ∂μ) ≤ W) :
    |∫ ω, score ω * dR ω ∂μ| + |∫ ω, score ω * dT ω ∂μ| ≤ Real.sqrt (I * (H + 1) * W) := by
  let Y := fun ω => |dR ω| + |dT ω|
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hRabs : AEStronglyMeasurable (fun ω => |dR ω|) μ := by
    simpa only [Real.norm_eq_abs] using hR.norm
  have hTabs : AEStronglyMeasurable (fun ω => |dT ω|) μ := by
    simpa only [Real.norm_eq_abs] using hT.norm
  have hYm : AEStronglyMeasurable Y μ := hRabs.add hTabs
  have hYbound : ∀ᵐ ω ∂μ, Y ω ≤ H + 1 := by
    filter_upwards [hRbound, hTbound] with ω hωR hωT
    exact add_le_add hωR hωT
  have hYnorm : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ H + 1 := hYbound.mono fun ω hω => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hY0 ω)] using hω
  have hYL2 : MemLp Y 2 μ := (memLp_top_of_bound hYm (H + 1) hYnorm).mono_exponent le_top
  have hYI : Integrable Y μ := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hYL2
  have hY2 : Integrable (fun ω => Y ω ^ 2) μ := (memLp_two_iff_integrable_sq hYm).mp hYL2
  have hs2 : Integrable (fun ω => score ω ^ 2) μ :=
    (memLp_two_iff_integrable_sq hscore.aestronglyMeasurable).mp hscore
  have hProducts := score_products_integrable μ hscore hR hT hRbound hTbound
  have hAR : Integrable (fun ω => |score ω * dR ω|) μ := hProducts.1.abs
  have hAT : Integrable (fun ω => |score ω * dT ω|) μ := hProducts.2.abs
  have hRCS : |∫ ω, score ω * dR ω ∂μ| ≤ ∫ ω, |score ω * dR ω| ∂μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => score ω * dR ω)
  have hTCS : |∫ ω, score ω * dT ω ∂μ| ≤ ∫ ω, |score ω * dT ω| ∂μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => score ω * dT ω)
  have hTriangle : |∫ ω, score ω * dR ω ∂μ| + |∫ ω, score ω * dT ω ∂μ| ≤
      ∫ ω, |score ω| * Y ω ∂μ := by
    calc
      _ ≤ (∫ ω, |score ω * dR ω| ∂μ) + ∫ ω, |score ω * dT ω| ∂μ := add_le_add hRCS hTCS
      _ = ∫ ω, |score ω| * Y ω ∂μ := by
        rw [← integral_add hAR hAT]
        apply integral_congr_ae
        exact Eventually.of_forall fun ω => by dsimp [Y]; rw [abs_mul, abs_mul]; ring
  have hAbsY : ∀ ω, |Y ω| = Y ω := fun ω => abs_of_nonneg (hY0 ω)
  have hHolder := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (show MemLp score (ENNReal.ofReal (2 : ℝ)) μ by simpa using hscore)
    (show MemLp Y (ENNReal.ofReal (2 : ℝ)) μ by simpa using hYL2)
  have hCS : (∫ ω, |score ω| * Y ω ∂μ) ≤
      Real.sqrt (∫ ω, score ω ^ 2 ∂μ) * Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := by
    simpa only [Real.norm_eq_abs, hAbsY, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using hHolder
  have hSquare : (∫ ω, Y ω ^ 2 ∂μ) ≤ (H + 1) * W := by
    calc
      _ ≤ ∫ ω, (H + 1) * Y ω ∂μ := integral_mono_ae hY2 (hYI.const_mul (H + 1)) (by
        filter_upwards [hYbound] with ω hω
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hω (hY0 ω))
      _ = (H + 1) * (∫ ω, Y ω ∂μ) := integral_const_mul _ _
      _ ≤ (H + 1) * W := mul_le_mul_of_nonneg_left hMean (by linarith)
  have hI0 : 0 ≤ I := (integral_nonneg fun ω => sq_nonneg (score ω)).trans hInfo
  calc
    _ ≤ Real.sqrt (∫ ω, score ω ^ 2 ∂μ) * Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := hTriangle.trans hCS
    _ ≤ Real.sqrt I * Real.sqrt ((H + 1) * W) :=
      mul_le_mul (Real.sqrt_le_sqrt hInfo) (Real.sqrt_le_sqrt hSquare) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (I * (H + 1) * W) := by rw [← Real.sqrt_mul hI0]; congr 1; ring

/-- `cor:score-stability`'s numerical form, assuming the coupled outcome-error bound.
Centering of a likelihood score is not needed for this analytic inequality. -/
theorem score_stability_bound_paper {score dR dT : Ω → ℝ} {H I W : ℝ} (hH : 0 ≤ H)
    (hscore : MemLp score 2 μ) (hR : AEStronglyMeasurable dR μ) (hT : AEStronglyMeasurable dT μ)
    (hRbound : ∀ᵐ ω ∂μ, |dR ω| ≤ H) (hTbound : ∀ᵐ ω ∂μ, |dT ω| ≤ 1)
    (hInfo : (∫ ω, score ω ^ 2 ∂μ) ≤ I)
    (hMean : (∫ ω, (|dR ω| + |dT ω|) ∂μ) ≤ W) :
    |∫ ω, score ω * dR ω ∂μ| + |∫ ω, score ω * dT ω ∂μ| ≤ Real.sqrt (2 * I * (H + 1) * W) := by
  have hI0 : 0 ≤ I := (integral_nonneg fun ω => sq_nonneg (score ω)).trans hInfo
  have hW0 : 0 ≤ W := (integral_nonneg fun ω => add_nonneg (abs_nonneg (dR ω)) (abs_nonneg (dT ω))).trans hMean
  have hprod : 0 ≤ I * (H + 1) * W := mul_nonneg (mul_nonneg hI0 (by linarith)) hW0
  exact (score_stability_bound μ hH hscore hR hT hRbound hTbound hInfo hMean).trans
    (Real.sqrt_le_sqrt (by nlinarith))

end ScoreBounds
end ProphetSecretary.Stability

