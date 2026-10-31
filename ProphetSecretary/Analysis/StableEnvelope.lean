import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A stable envelope for a supremum of payoffs

The fixed-payoff expansion and continuity of its derivative at small base regret
are separate premises. No parameter-dependent optimizer is differentiated or
assumed to exist. This is the analytic argument in `eq:env-two-sided`.
-/

open Set Filter
open scoped Topology

namespace ProphetSecretary.Analysis

lemma supremum_base_value {ι : Type*} (J : ℝ → ι → ℝ) (i₀ : ι)
    (hbase : ∀ i, J 0 i ≤ J 0 i₀) : sSup (range (J 0)) = J 0 i₀ := by
  apply le_antisymm
  · exact csSup_le ⟨J 0 i₀, mem_range_self i₀⟩ (by rintro _ ⟨i, rfl⟩; exact hbase i)
  · exact le_csSup ⟨J 0 i₀, by rintro _ ⟨i, rfl⟩; exact hbase i⟩ (mem_range_self i₀)

/-- Explicit two-sided envelope error before taking a limit. The radius condition
separates policies with large base regret from those whose derivative is stable. -/
lemma stable_envelope_error {ι : Type*} (J : ℝ → ι → ℝ) (D : ι → ℝ) (i₀ : ι)
    {A B θ ε η : ℝ} (hε : 0 ≤ ε)
    (hbase : ∀ i, J 0 i ≤ J 0 i₀) (hD : ∀ i, |D i| ≤ B)
    (hTaylor : ∀ i, |J θ i - J 0 i - θ * D i| ≤ A * θ ^ 2)
    (hStable : ∀ i, J 0 i₀ - J 0 i ≤ η → |D i - D i₀| ≤ ε)
    (hsmall : 2 * B * |θ| ≤ η) :
    |sSup (range (J θ)) - J 0 i₀ - θ * D i₀| ≤ ε * |θ| + A * θ ^ 2 := by
  have hterm (i : ι) : θ * D i ≤ |θ| * B := by
    calc
      _ ≤ |θ * D i| := le_abs_self _
      _ = |θ| * |D i| := abs_mul _ _
      _ ≤ |θ| * B := mul_le_mul_of_nonneg_left (hD i) (abs_nonneg _)
  have hbdd : BddAbove (range (J θ)) := by
    refine ⟨J 0 i₀ + |θ| * B + A * θ ^ 2, ?_⟩
    rintro _ ⟨i, rfl⟩
    have ht := (abs_le.mp (hTaylor i)).2
    have hi := hbase i
    have hm := hterm i
    linarith
  have hupper : sSup (range (J θ)) ≤
      J 0 i₀ + θ * D i₀ + ε * |θ| + A * θ ^ 2 := by
    apply csSup_le ⟨J θ i₀, mem_range_self i₀⟩
    rintro _ ⟨i, rfl⟩
    have ht := (abs_le.mp (hTaylor i)).2
    have hi := hbase i
    by_cases hr : J 0 i₀ - J 0 i ≤ η
    · have hd := hStable i hr
      have hm : θ * (D i - D i₀) ≤ |θ| * ε := by
        calc
          _ ≤ |θ * (D i - D i₀)| := le_abs_self _
          _ = |θ| * |D i - D i₀| := abs_mul _ _
          _ ≤ |θ| * ε := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      nlinarith
    · have hd : |D i - D i₀| ≤ 2 * B :=
        (abs_sub _ _).trans (by linarith [hD i, hD i₀])
      have hm : θ * (D i - D i₀) ≤ |θ| * (2 * B) := by
        calc
          _ ≤ |θ * (D i - D i₀)| := le_abs_self _
          _ = |θ| * |D i - D i₀| := abs_mul _ _
          _ ≤ |θ| * (2 * B) := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      have hnonneg := mul_nonneg hε (abs_nonneg θ)
      nlinarith
  have hlower := le_csSup hbdd (mem_range_self i₀)
  have ht0 := (abs_le.mp (hTaylor i₀)).1
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hε (abs_nonneg θ)]

/-- Stable fixed-policy derivatives and a uniform quadratic remainder imply the
derivative of the reoptimized value. Only the base optimum must be attained. -/
theorem hasDerivAt_supremum_of_stable_payoffs {ι : Type*}
    (J : ℝ → ι → ℝ) (D : ι → ℝ) (i₀ : ι) {A B ρ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hbase : ∀ i, J 0 i ≤ J 0 i₀) (hD : ∀ i, |D i| ≤ B)
    (hTaylor : ∀ θ, |θ| ≤ ρ → ∀ i,
      |J θ i - J 0 i - θ * D i| ≤ A * θ ^ 2)
    (hStable : ∀ ε, 0 < ε → ∃ η, 0 < η ∧
      ∀ i, J 0 i₀ - J 0 i ≤ η → |D i - D i₀| ≤ ε) :
    HasDerivAt (fun θ => sSup (range (J θ))) (D i₀) 0 := by
  apply hasDerivAt_iff_isLittleO.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  obtain ⟨η, hη, hStableη⟩ := hStable (ε / 2) (by positivity)
  let r₁ := η / (2 * B + 1)
  let r₂ := ε / (2 * (A + 1))
  have hr₁ : 0 < r₁ := by dsimp [r₁]; positivity
  have hr₂ : 0 < r₂ := by dsimp [r₂]; positivity
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hρ) hρ,
    Ioo_mem_nhds (neg_lt_zero.mpr hr₁) hr₁,
    Ioo_mem_nhds (neg_lt_zero.mpr hr₂) hr₂] with θ hθ hθ₁ hθ₂
  have hθρ : |θ| ≤ ρ := (abs_lt.mpr hθ).le
  have hsmall : 2 * B * |θ| ≤ η := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2 * B + 1)).mp (abs_lt.mpr hθ₁).le
    nlinarith [abs_nonneg θ]
  have hscale : A * |θ| ≤ ε / 2 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2 * (A + 1))).mp (abs_lt.mpr hθ₂).le
    nlinarith [abs_nonneg θ]
  have hquad : A * θ ^ 2 ≤ (ε / 2) * |θ| := by
    have ht := mul_le_mul_of_nonneg_right hscale (abs_nonneg θ)
    nlinarith [sq_abs θ]
  have h := stable_envelope_error J D i₀ (by positivity : 0 ≤ ε / 2)
    hbase hD (hTaylor θ hθρ) hStableη hsmall
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, smul_eq_mul,
    supremum_base_value J i₀ hbase]
  nlinarith

end ProphetSecretary.Analysis
