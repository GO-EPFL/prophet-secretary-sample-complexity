import ProphetSecretary.Probability.MartingaleMoments
import ProphetSecretary.Analysis.PosteriorIncrement

/-!
# Posterior movement relative to an observed pilot

Martingale orthogonality gives the squared-distance increment identity used
in `eq:bayes-brier-identity`. Predictability and all integrability obligations
are explicit. The deterministic small-increment lemma then selects an index
from expectations, before any observations are realized.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Probability

private lemma unit_interval_abs_sub_le_one {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : |x-y| ≤ 1 :=
  abs_le.mpr ⟨by linarith only [hx.1,hy.2],by linarith only [hx.2,hy.1]⟩

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {S : ℕ → Ω → ℝ}

private lemma integrable_unit_square_distance {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hx : ∀ᵐ ω ∂μ, X ω ∈ Icc (0 : ℝ) 1) (hy : ∀ᵐ ω ∂μ, Y ω ∈ Icc (0 : ℝ) 1) :
    Integrable (fun ω => (X ω-Y ω)^2) μ := by
  apply Integrable.of_bound ((hX.sub hY).pow_const 2).aestronglyMeasurable 1
  filter_upwards [hx,hy] with ω hx hy
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_one_iff_abs_le_one _).mpr (unit_interval_abs_sub_le_one hx hy)

theorem martingale_square_distance_increment (hS : Martingale S ℱ μ)
    (hUnit : ∀ k, ∀ᵐ ω ∂μ, S k ω ∈ Icc (0 : ℝ) 1)
    {Y : Ω → ℝ} {l j : ℕ} (hY : StronglyMeasurable[ℱ l] Y)
    (hYU : ∀ᵐ ω ∂μ, Y ω ∈ Icc (0 : ℝ) 1) (hlj : l ≤ j) :
    (∫ ω, (S (j+1) ω-Y ω)^2 ∂μ) - (∫ ω, (S j ω-Y ω)^2 ∂μ) =
      ∫ ω, (S (j+1) ω-S j ω)^2 ∂μ := by
  have hSj : Measurable (S j) := ((hS.stronglyAdapted j).mono (ℱ.le j)).measurable
  have hSn : Measurable (S (j+1)) := ((hS.stronglyAdapted (j+1)).mono (ℱ.le (j+1))).measurable
  have hYm : Measurable Y := (hY.mono (ℱ.le l)).measurable
  let g := fun ω => S j ω-Y ω
  let G := fun ω => g ω*(S (j+1) ω-S j ω)
  have hg : StronglyMeasurable[ℱ j] g := (hS.stronglyAdapted j).sub (hY.mono (ℱ.mono hlj))
  have hgB : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1 := by
    filter_upwards [hUnit j,hYU] with ω hω hy
    exact (Real.norm_eq_abs _).trans_le (unit_interval_abs_sub_le_one hω hy)
  have hG : Integrable G μ := ((hS.integrable (j+1)).sub (hS.integrable j)).bdd_mul
    (hg.mono (ℱ.le j)).aestronglyMeasurable hgB
  have hG0 : (∫ ω, G ω ∂μ) = 0 := integral_predictable_mul_increment_zero hS j hg hG
  have hOld := integrable_unit_square_distance hSj hYm (hUnit j) hYU
  have hInc := integrable_unit_square_distance hSn hSj (hUnit (j+1)) (hUnit j)
  have hPoint : (fun ω => (S (j+1) ω-Y ω)^2) =
      (fun ω => ((S j ω-Y ω)^2+2*G ω)+(S (j+1) ω-S j ω)^2) := by
    funext ω
    dsimp only [G,g]
    ring
  have hSumInt : Integrable (fun ω => (S j ω-Y ω)^2+2*G ω) μ := hOld.add (hG.const_mul 2)
  have heq : (∫ ω, (S (j+1) ω-Y ω)^2 ∂μ) =
      (∫ ω, (S j ω-Y ω)^2 ∂μ) + ∫ ω, (S (j+1) ω-S j ω)^2 ∂μ := by
    rw [hPoint,integral_add hSumInt hInc,
      integral_add hOld (hG.const_mul 2),integral_const_mul,hG0,mul_zero,add_zero]
  linarith only [heq]

lemma unit_square_distance_mean_mem {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hx : ∀ᵐ ω ∂μ, X ω ∈ Icc (0 : ℝ) 1) (hy : ∀ᵐ ω ∂μ, Y ω ∈ Icc (0 : ℝ) 1) :
    (∫ ω, (X ω-Y ω)^2 ∂μ) ∈ Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg (fun _ => sq_nonneg _),?_⟩
  have hI := integrable_unit_square_distance hX hY hx hy
  have hBound : ∀ᵐ ω ∂μ, (X ω-Y ω)^2 ≤ 1 := by
    filter_upwards [hx,hy] with ω hx hy
    exact (sq_le_one_iff_abs_le_one _).mpr (unit_interval_abs_sub_le_one hx hy)
  have hUpper := integral_mono_ae hI (integrable_const (1 : ℝ)) hBound
  simpa using hUpper

/-- The selected index is deterministic: it is outside all expectations. -/
theorem exists_small_martingale_movement (hS : Martingale S ℱ μ)
    (hUnit : ∀ k, ∀ᵐ ω ∂μ, S k ω ∈ Icc (0 : ℝ) 1)
    {Y : Ω → ℝ} {base m : ℕ} (hY : StronglyMeasurable[ℱ base] Y)
    (hYU : ∀ᵐ ω ∂μ, Y ω ∈ Icc (0 : ℝ) 1) (hm : 8 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ j < m, Real.sqrt (∫ ω, (S (base+j+1) ω-S (base+j) ω)^2 ∂μ) ≤
      α*(∫ ω, (S (base+j) ω-Y ω)^2 ∂μ)+8/(α*(m : ℝ)) := by
  let v := fun j : ℕ => ∫ ω, (S (base+j) ω-Y ω)^2 ∂μ
  have hYm : Measurable Y := (hY.mono (ℱ.le base)).measurable
  have hv (j : ℕ) : v j ∈ Icc (0 : ℝ) 1 := unit_square_distance_mean_mem
    ((hS.stronglyAdapted (base+j)).mono (ℱ.le (base+j))).measurable hYm (hUnit (base+j)) hYU
  have hIdentity (j : ℕ) : v (j+1)-v j =
      ∫ ω, (S (base+j+1) ω-S (base+j) ω)^2 ∂μ := by
    have h := martingale_square_distance_increment (j := base+j) hS hUnit hY hYU (Nat.le_add_right base j)
    simpa only [v,Nat.add_assoc] using h
  have hStep (j : ℕ) (_hj : j < m) : v j ≤ v (j+1) := by
    have h := hIdentity j
    have h0 : 0 ≤ ∫ ω, (S (base+j+1) ω-S (base+j) ω)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    linarith only [h,h0]
  obtain ⟨j,hj,hBound⟩ := ProphetSecretary.Analysis.exists_small_posterior_increment hm v (fun j _ => hv j) hStep hα hα1
  rw [hIdentity j] at hBound
  exact ⟨j,hj,hBound⟩

/-- Actual conditional-expectation posterior of a bounded hidden target. -/
noncomputable def conditionalPosterior (Q : Ω → ℝ) (F : Filtration ℕ m0) (P : Measure Ω) (k : ℕ) : Ω → ℝ :=
  P[Q | F k]

lemma conditionalPosterior_martingale (Q : Ω → ℝ) :
    Martingale (conditionalPosterior Q ℱ μ) ℱ μ := martingale_condExp Q ℱ μ

lemma conditionalPosterior_mem_unit {Q : Ω → ℝ} (hQ : Measurable Q)
    (hQU : ∀ᵐ ω ∂μ, Q ω ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    ∀ᵐ ω ∂μ, conditionalPosterior Q ℱ μ k ω ∈ Icc (0 : ℝ) 1 := by
  have hQI : Integrable Q μ := Integrable.of_bound hQ.aestronglyMeasurable 1 (by
    filter_upwards [hQU] with ω hω
    simpa only [Real.norm_eq_abs,abs_of_nonneg hω.1] using hω.2)
  have h0 := condExp_nonneg (m := ℱ k) (hQU.mono (fun _ h => h.1))
  have h1 := condExp_mono (m := ℱ k) hQI (integrable_const (1 : ℝ)) (hQU.mono (fun _ h => h.2))
  rw [condExp_const (ℱ.le k) (1 : ℝ)] at h1
  filter_upwards [h0,h1] with ω h0 h1
  exact ⟨h0,h1⟩

/-- `eq:bayes-brier-identity` for the actual posterior of any bounded target
and any pilot observed by the stated time. -/
theorem conditionalPosterior_square_distance_increment {Q : Ω → ℝ} (hQ : Measurable Q)
    (hQU : ∀ᵐ ω ∂μ, Q ω ∈ Icc (0 : ℝ) 1)
    {Y : Ω → ℝ} {l j : ℕ} (hY : StronglyMeasurable[ℱ l] Y)
    (hYU : ∀ᵐ ω ∂μ, Y ω ∈ Icc (0 : ℝ) 1) (hlj : l ≤ j) :
    (∫ ω, (conditionalPosterior Q ℱ μ (j+1) ω-Y ω)^2 ∂μ) -
      (∫ ω, (conditionalPosterior Q ℱ μ j ω-Y ω)^2 ∂μ) =
      ∫ ω, (conditionalPosterior Q ℱ μ (j+1) ω-conditionalPosterior Q ℱ μ j ω)^2 ∂μ :=
  martingale_square_distance_increment (conditionalPosterior_martingale Q)
    (conditionalPosterior_mem_unit hQ hQU) hY hYU hlj

end ProphetSecretary.Probability
