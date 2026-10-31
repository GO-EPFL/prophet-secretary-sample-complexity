import ProphetSecretary.Model.LawRegularWorlds
import ProphetSecretary.Probability.WideWorldIntegration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Averaging the directional adaptation kernel
The old policy is held fixed. New-law expectations are rebased to the old
complete-world law before dominated convergence; the domination is uniform in
all residual offers and clocks of each fixed finite instance.
-/
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

theorem Instance.lawConditionalRegret_integral_kernel_limit (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (i : Fin n)
    (hL : ∀ᵐ ω : World n Unit ∂(P.likelihoodWidePath h hh hb hm θ).worldLaw (Measure.dirac ()),
      Tendsto (fun δ : ℝ ↦ P.lawConditionalRegret hw hc.le hbound h hh hb hm θ (θ + δ) i ω / δ ^ 2)
        (𝓝[≠] 0) (𝓝 ((∑ A : Finset (Fin n), P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω) / 2))) :
    Tendsto (fun δ : ℝ ↦ (∫ ω : World n Unit,
      P.lawConditionalRegret hw hc.le hbound h hh hb hm θ (θ + δ) i ω
      ∂(P.likelihoodWidePath h hh hb hm (θ + δ)).worldLaw (Measure.dirac ())) / δ ^ 2)
      (𝓝[≠] 0) (𝓝 (∫ ω : World n Unit,
        (∑ A : Finset (Fin n), P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω) / 2
        ∂(P.likelihoodWidePath h hh hb hm θ).worldLaw (Measure.dirac ()))) := by
  have hθabs : |θ| ≤ 1 / 2 := abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩
  let Q := P.likelihoodWidePath h hh hb hm θ
  let s := fun j ↦ recenteredUnitScore (h j) θ
  have hsM (j : Fin n) : Measurable (s j) := measurable_recenteredUnitScore (hh j) θ
  have hsB (j : Fin n) : ∀ᵐ a ∂Q.law j, |s j a| ≤ 1 := by
    dsimp only [Q]
    rw [P.likelihoodWidePath_of_mem h hh hb hm hθabs]
    exact recenteredUnitScore_bound (hb j) hθabs
  have hScores : ∀ᵐ ω : World n Unit ∂Q.worldLaw (Measure.dirac ()), ∀ j, |s j (ω.1 j)| ≤ 1 := by
    have hp : MeasurePreserving (fun ω : World n Unit ↦ ω.1) (Q.worldLaw (Measure.dirac ())) Q.valuesLaw := measurePreserving_fst
    exact hp.quasiMeasurePreserving.ae (ae_all_iff.mpr (fun j ↦ (measurePreserving_eval Q.law j).quasiMeasurePreserving.ae (hsB j)))
  let C := 8 * (1 + (n : ℝ)) * (2 * (w * H + c) * (n : ℝ)) ^ 2 / c
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hNear : ∀ᶠ δ : ℝ in 𝓝[≠] 0, |2 * δ| ≤ 1 / 4 ∧ |θ + δ| ≤ 1 / 2 := by
    have hAdd : Tendsto (fun δ : ℝ ↦ θ + δ) (𝓝 0) (𝓝 θ) := by
      have hC : Continuous (fun δ : ℝ ↦ θ + δ) := continuous_const.add continuous_id
      simpa only [add_zero] using hC.tendsto 0
    have hSmall : ∀ᶠ δ : ℝ in 𝓝 0, δ ∈ Icc (-(1 / 8) : ℝ) (1 / 8) :=
      Icc_mem_nhds (by norm_num) (by norm_num)
    have hInside : ∀ᶠ δ : ℝ in 𝓝 0, θ + δ ∈ Icc (-(1 / 2) : ℝ) (1 / 2) :=
      hAdd (Icc_mem_nhds hθ.1 hθ.2)
    filter_upwards [hSmall.filter_mono nhdsWithin_le_nhds, hInside.filter_mono nhdsWithin_le_nhds] with δ hδ hNew
    exact ⟨abs_le.mpr ⟨by linarith [hδ.1], by linarith [hδ.2]⟩, abs_le.mpr hNew⟩
  let F := fun δ (ω : World n Unit) ↦ likelihood s (2 * δ) ω.1 *
    (P.lawConditionalRegret hw hc.le hbound h hh hb hm θ (θ + δ) i ω / δ ^ 2)
  have hD := tendsto_integral_filter_of_dominated_convergence
    (μ := Q.worldLaw (Measure.dirac ())) (F := F) (fun _ ↦ (5 / 4 : ℝ) ^ n * C)
    (Filter.Eventually.of_forall (fun δ ↦
      ((((measurable_likelihood hsM (2 * δ)).comp measurable_fst).mul
        ((P.measurable_lawConditionalRegret hw hc.le hbound h hh hb hm θ (θ + δ) i).div_const (δ ^ 2))).aestronglyMeasurable)))
    (by
      filter_upwards [hNear, P.eventually_lawConditionalRegret_bound hw hc hH hbound h hh hb hm hθ] with δ hN hB
      filter_upwards [hScores] with ω hω
      change |likelihood s (2 * δ) ω.1 * (_ / δ ^ 2)| ≤ _
      rw [abs_mul]
      exact mul_le_mul (likelihood_abs_le_card hN.1 hω) (hB i ω) (abs_nonneg _) (by positivity))
    (integrable_const _) (by
      filter_upwards [hL] with ω hω
      have hT := ((tendsto_likelihood_zero s ω.1).mono_left nhdsWithin_le_nhds).mul hω
      simpa only [one_mul] using hT)
  apply hD.congr'
  filter_upwards [hNear] with δ hN
  rw [P.integral_likelihoodWidePath_rebase (Measure.dirac ()) h hh hb hm hθabs hN.1 hN.2]
  rw [← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω ↦ by dsimp only [F, s]; ring)

end ProphetSecretary.Model
