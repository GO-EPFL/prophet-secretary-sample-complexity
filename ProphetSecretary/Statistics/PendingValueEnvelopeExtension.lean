import ProphetSecretary.Statistics.StateContinuationRescaling
import ProphetSecretary.Probability.RationalEnvelopeExtension

/-!
# Extending a countable later-time and scalar envelope

For fixed offer laws and clocks, value is continuous in a clipped scalar
coefficient and has the proved left limits in elapsed time. Two deterministic
unit-interval enumerations therefore extend a common envelope to every later
physical time and every interval coefficient. Zero remaining horizon is kept.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.continuous_continuation_clippedScalar (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (A : Finset (Fin n)) {u : ℝ} (hu : 0 ≤ u)
    (lo hi : ℝ) :
    Continuous (fun η : ℝ => P.continuationValue A u 1 (max 0 (lo+(hi-lo)*η))) := by
  have hA := P.restrictTo_integrable_maximum A hP
  have hV := optimalScalarValue_durationWeight_continuousOn (P.restrictTo A) hA (by norm_num : (0 : ℝ) ≤ 1)
  have hc : Continuous (fun η : ℝ => max 0 (lo+(hi-lo)*η) * u) :=
    (continuous_const.max (continuous_const.add (continuous_const.mul continuous_id))).mul continuous_const
  exact hV.comp_continuous hc (fun η => mul_nonneg (le_max_left _ _) hu)

/-- Deterministic dense-grid extension, used after a countable intersection of
actual fixed-parameter probability-one domination events. -/
theorem pendingValueError_extend_unitGrid (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    {lo hi t₀ B : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (ht₀ : t₀ < 1) (u : Fin n → ℝ)
    (hgrid : ∀ j l,
      let t := t₀+(1-t₀)*ProphetSecretary.Probability.rationalObservationTime j
      let z := lo+(hi-lo)*ProphetSecretary.Probability.rationalObservationTime l
      |Q.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (max 0 (1-t)) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (max 0 (1-t)) 1 z| ≤ B) :
    ∀ t ∈ Icc t₀ 1, ∀ z ∈ Icc lo hi,
      |Q.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (max 0 (1-t)) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (max 0 (1-t)) 1 z| ≤ B := by
  let T : ℝ → ℝ := fun θ => t₀+(1-t₀)*θ
  let G : ℝ → ℝ → ℝ := fun t z =>
    |Q.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (max 0 (1-t)) 1 z -
      P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (max 0 (1-t)) 1 z|
  have hscalar (j : ℕ) : ∀ z ∈ Icc lo hi, G (T (ProphetSecretary.Probability.rationalObservationTime j)) z ≤ B := by
    let tj := T (ProphetSecretary.Probability.rationalObservationTime j)
    let F : ℝ → ℝ := fun η => G tj (max 0 (lo+(hi-lo)*η))
    have hFc : Continuous F := continuous_abs.comp
      ((Q.continuous_continuation_clippedScalar hQ (ProphetSecretary.Probability.pendingClockSet tj u) (le_max_left 0 (1-tj)) lo hi).sub
        (P.continuous_continuation_clippedScalar hP (ProphetSecretary.Probability.pendingClockSet tj u) (le_max_left 0 (1-tj)) lo hi))
    have hFg (l : ℕ) : F (ProphetSecretary.Probability.rationalObservationTime l) ≤ B := by
      have hl := ProphetSecretary.Probability.rationalObservationTime_mem l
      have hz0 : 0 ≤ lo+(hi-lo)*ProphetSecretary.Probability.rationalObservationTime l :=
        add_nonneg hlo (mul_nonneg (sub_nonneg.mpr hlohi) hl.1)
      change G tj (max 0 (lo+(hi-lo)*ProphetSecretary.Probability.rationalObservationTime l)) ≤ _
      rw [max_eq_right hz0]
      exact hgrid j l
    have hFb := ProphetSecretary.Probability.unitInterval_bound_of_leftLimits
      (fun η _ => hFc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hFg
    intro z hz
    obtain ⟨η,hη,hηz⟩ := exists_unitInterval_affine hlohi hz
    have hz0 : 0 ≤ z := hlo.trans hz.1
    have hb := hFb η hη
    change G tj (max 0 (lo+(hi-lo)*η)) ≤ B at hb
    rw [hηz,max_eq_right hz0] at hb
    exact hb
  intro t ht z hz
  have hz0 : 0 ≤ z := hlo.trans hz.1
  let F : ℝ → ℝ := fun θ => G (T θ) z
  have hlim (θ : ℝ) : Tendsto F (𝓝[<] θ) (𝓝 (F θ)) := by
    have hPhys := continuous_abs.continuousAt.tendsto.comp
      ((ProphetSecretary.Probability.pendingContinuationValue_tendsto_left Q hQ hz0 u (T θ)).sub
        (ProphetSecretary.Probability.pendingContinuationValue_tendsto_left P hP hz0 u (T θ)))
    exact hPhys.comp (ProphetSecretary.Probability.tendsto_positive_affine_left t₀ (1-t₀) θ (sub_pos.mpr ht₀))
  have hFb := ProphetSecretary.Probability.unitInterval_bound_of_leftLimits (fun θ _ => hlim θ)
    (fun j => hscalar j z hz)
  obtain ⟨θ,hθ,hθt⟩ := exists_unitInterval_affine ht₀.le ht
  have hb := hFb θ hθ
  change G (t₀+(1-t₀)*θ) z ≤ B at hb
  rw [hθt] at hb
  exact hb

end ProphetSecretary.Model
