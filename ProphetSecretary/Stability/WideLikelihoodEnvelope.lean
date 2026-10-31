import ProphetSecretary.Probability.WideLikelihoodPath

/-!
# Likelihood envelopes at every interior parameter

The score is re-centered at the actual base law before applying the proved
fixed-base envelope. The larger parameter neighborhood contains both endpoints
of the manuscript's closed quarter interval.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem Instance.hasDerivAt_optimalScalarValue_likelihoodWidePath (P : Instance n)
    {w c H : ℝ} (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    let Q := P.likelihoodWideTilt h hh hb hm θ (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩)
    let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWideTilt_bounded h hh hb hm θ _ hbound)
    HasDerivAt (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c)
      (∑ i : Fin n, ∫ a, tiltedScore (h i) θ a * Q.marginalPremium hQ hw hc.le i a ∂Q.law i) θ := by
  let hθ' := abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩
  let Q := P.likelihoodWideTilt h hh hb hm θ hθ'
  have hQBound := P.likelihoodWideTilt_bounded h hh hb hm θ hθ' hbound
  let hQ := Q.integrable_maximum_of_bounded hQBound
  let s := fun i ↦ recenteredUnitScore (h i) θ
  have hsM (i : Fin n) : Measurable (s i) := measurable_recenteredUnitScore (hh i) θ
  have hsB (i : Fin n) : ∀ᵐ a ∂Q.law i, |s i a| ≤ 1 := recenteredUnitScore_bound (hb i) hθ'
  have hs0 (i : Fin n) : ∫ a, s i a ∂Q.law i = 0 := recenteredUnitScore_centered (hh i) (hb i) (hm i) hθ'
  let L := ∑ i : Fin n, ∫ a, s i a * Q.marginalPremium hQ hw hc.le i a ∂Q.law i
  have hD : HasDerivAt (fun δ ↦ optimalScalarValue (Q.likelihoodPath s hsM hsB hs0 δ) w c) L 0 :=
    Q.hasDerivAt_optimalScalarValue_marginalPremium hw hc hH hQBound s hsM hsB hs0
  have hInner : HasDerivAt (fun t : ℝ ↦ 2 * (t - θ)) 2 θ := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id θ).sub_const θ).const_mul 2
  have hD' : HasDerivAt (fun δ ↦ optimalScalarValue (Q.likelihoodPath s hsM hsB hs0 δ) w c) L (2 * (θ - θ)) := by
    simpa only [sub_self, mul_zero] using hD
  have hComp := hD'.comp θ hInner
  have hCoeff : L * 2 = ∑ i : Fin n, ∫ a, tiltedScore (h i) θ a * Q.marginalPremium hQ hw hc.le i a ∂Q.law i := by
    dsimp only [L]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun a ↦ by dsimp only [s, recenteredUnitScore]; ring)
  rw [hCoeff] at hComp
  apply hComp.congr_of_eventuallyEq
  have hnear : ∀ᶠ t : ℝ in 𝓝 θ,
      t ∈ Icc (-(1 / 2) : ℝ) (1 / 2) ∧ |2 * (t - θ)| ≤ 1 / 4 := by
    have hclose : ∀ᶠ t : ℝ in 𝓝 θ, t ∈ Icc (θ - 1 / 8) (θ + 1 / 8) :=
      Icc_mem_nhds (by linarith) (by linarith)
    filter_upwards [Icc_mem_nhds hθ.1 hθ.2, hclose] with t ht hc'
    exact ⟨ht, abs_le.mpr ⟨by linarith [hc'.1], by linarith [hc'.2]⟩⟩
  filter_upwards [hnear] with t ht
  have hAbsT : |t| ≤ 1 / 2 := abs_le.mpr ⟨ht.1.1, ht.1.2⟩
  dsimp only [Function.comp_apply]
  rw [P.likelihoodWidePath_of_mem h hh hb hm hAbsT, Q.likelihoodPath_of_mem s hsM hsB hs0 ht.2]
  have hadd : θ + (t - θ) = t := by ring
  have he := P.likelihoodWideTilt_rebase h hh hb hm hθ' ht.2
    (show |θ + (t - θ)| ≤ 1 / 2 by simpa only [hadd] using hAbsT)
  have he' : Q.likelihoodTilt s hsM hsB hs0 (2 * (t - θ)) ht.2 =
      P.likelihoodWideTilt h hh hb hm t hAbsT := by
    simpa only [hadd] using he
  rw [he']

end ProphetSecretary.Model
