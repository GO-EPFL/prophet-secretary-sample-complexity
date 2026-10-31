import ProphetSecretary.Limiting.ScheduledVirtualTail
import ProphetSecretary.Limiting.DirectCanonicalIndividualLimit
import ProphetSecretary.Limiting.DirectIndividualMaximumScore

/-!
# Canonical score limits for the actual chosen direct schedule

The exact scheduled virtual marginals satisfy the positive-level intensity
and square-rarity conditions. The full-policy value limit and common tail
profile therefore identify reward and duration score limits for the actual
finite canonical optimizers. Maximum-score convergence is established
separately through perturbed benchmarks.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def directCanonicalPolicy (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (m : ℕ) : RandomizedPolicy (m+B.directVirtualCount hZero m) :=
  (B.directFiniteApproximation hZero m).valuePolicy
    ((B.directFiniteApproximation hZero m).integrable_maximum_of_bounded (B.directFiniteApproximation_bounded hZero m)) hw.le hc.le

private lemma valuePolicy_congr_instance {n : ℕ} {P Q : Model.Instance n} (hEq : P=Q)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) : P.valuePolicy hP hw hc=Q.valuePolicy hQ hw hc := by
  cases hEq
  rfl

theorem directScheduled_canonical_individual_score_limits (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (hSum : w+c=1) (i : ℕ) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun m => (B.directCanonicalPolicy hZero hw hc m).expectedRewardScore (B.directFiniteApproximation hZero m)
      (directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f)) atTop
      (𝓝 (∫ v : CompleteWorld Unit, centeredBoundedScore (B.individuals i : Measure ℝ) f (v.2.1 i)*
        (B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun m => (B.directCanonicalPolicy hZero hw hc m).expectedDurationScore (B.directFiniteApproximation hZero m)
      (directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f)) atTop
      (𝓝 (∫ v : CompleteWorld Unit, centeredBoundedScore (B.individuals i : Measure ℝ) f (v.2.1 i)*
        (B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) := by
  let κ := fun m => (B.directVirtualOfferLaw hZero m : Measure ℝ)
  let hκ := fun m => (B.directVirtualOfferLaw_bounds hZero m).mono (fun _ hx => hx.1)
  let Q := fun m => B.directVirtualOfferInstance hZero m
  let P := fun m => (B.individualPrefix m).appendIndependent (Q m)
  have hCap (m : ℕ) : ∀ᵐ x ∂κ m, x≤(B.cap : ℝ) :=
    (B.directVirtualOfferLaw_bounds hZero m).mono (fun _ hx => hx.2)
  let hP := fun m => (P m).integrable_maximum_of_bounded
    ((B.individualPrefix m).appendIndependent_bounded (Q m)
      (fun j => (B.individual_supported j.val).mono (fun _ hx => hx.2)) (fun _ => hCap m))
  let π := fun m => (P m).valuePolicy (hP m) hw.le hc.le
  have hTail : ∀ m d, 0<d → (P m).tailCount d≤(B.totalTailMass d).toReal := by
    intro m d hd
    have h := B.directFiniteApproximation_tailCount_le hZero m hd
    rw [B.directFiniteApproximation_eq_appendVirtual hZero m] at h
    exact h
  have hV : Tendsto (fun m => Model.optimalScalarValue (P m) w c) atTop (𝓝 (B.optimalScalarValue w c)) := by
    have h := B.directFiniteApproximation_value_tendsto hZero hw.le hc.le
    simp_rw [B.directFiniteApproximation_eq_appendVirtual hZero] at h
    exact h
  have hLimits := B.direct_canonical_individual_score_limits hZero id (B.directVirtualCount hZero)
    tendsto_id (B.directVirtualCount_positive hZero) κ hκ hCap
    (B.directVirtualOfferLaw_threshold_tendsto hZero)
    (fun d hd => B.directVirtualOfferLaw_square_sum_tendsto hZero d hd.le)
    (fun d => (B.totalTailMass d).toReal) (fun _ _ => ENNReal.toReal_nonneg) hTail hw hc hSum hV i f
  have hCanon (m : ℕ) : B.directCanonicalPolicy hZero hw hc m=π m := by
    exact valuePolicy_congr_instance (B.directFiniteApproximation_eq_appendVirtual hZero m) _ _ hw.le hc.le
  have hReward (m : ℕ) : (π m).expectedRewardScore (P m)
      (directIndividualScore (B.individualPrefix m) (Q m) i f)=
      (B.directCanonicalPolicy hZero hw hc m).expectedRewardScore (B.directFiniteApproximation hZero m)
        (directIndividualScore (B.individualPrefix m) (Q m) i f) := by
    rw [←hCanon m,B.directFiniteApproximation_eq_appendVirtual hZero m]
  have hDuration (m : ℕ) : (π m).expectedDurationScore (P m)
      (directIndividualScore (B.individualPrefix m) (Q m) i f)=
      (B.directCanonicalPolicy hZero hw hc m).expectedDurationScore (B.directFiniteApproximation hZero m)
        (directIndividualScore (B.individualPrefix m) (Q m) i f) := by
    rw [←hCanon m,B.directFiniteApproximation_eq_appendVirtual hZero m]
  exact ⟨hLimits.1.congr hReward,hLimits.2.congr hDuration⟩

end ProphetSecretary.Limiting.CountableInstance
