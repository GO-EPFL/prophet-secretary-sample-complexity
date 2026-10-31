import ProphetSecretary.Limiting.DirectScheduledCloudProperties
import ProphetSecretary.Limiting.DirectCanonicalCloudLimit

/-!
# Canonical cloud-score limits for the actual direct schedule

The actual scheduled virtual marginals supply every positive-band geometry
hypothesis of the generic score limit. Discarding finitely many indices makes
the cutoff lie below the scored band; the final convergence is for the full
original sequence. No first-moment bound is introduced.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

private lemma canonical_scores_congr_instance {n : ℕ} {P Q : Instance n} (hEq : P=Q)
    (hP : Integrable Instance.maximum P.valuesLaw) (hQ : Integrable Instance.maximum Q.valuesLaw)
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) (score : Fin n → ℝ → ℝ) :
    (P.valuePolicy hP hw hc).expectedRewardScore P score=(Q.valuePolicy hQ hw hc).expectedRewardScore Q score ∧
    (P.valuePolicy hP hw hc).expectedDurationScore P score=(Q.valuePolicy hQ hw hc).expectedDurationScore Q score := by
  cases hEq
  exact ⟨rfl,rfl⟩

theorem directScheduled_canonical_cloud_score_limits (B : CountableInstance) (hZero : B.terminal=0)
    (b : ℝ) (hb : (B.terminal:ℝ)<b) (hAtom : B.intensity {b}=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (hNorm : w+c=1) :
    let π := fun m => (B.directFiniteApproximation hZero m).valuePolicy
      ((B.directFiniteApproximation hZero m).integrable_maximum_of_bounded (B.directFiniteApproximation_bounded hZero m)) hw.le hc.le
    Tendsto (fun m => (π m).expectedRewardScore (B.directFiniteApproximation hZero m)
      (B.directScheduledCloudScore hZero (Ioi b) m)) atTop
      (𝓝 (∫ v, B.bandScore (Ioi b) v*(B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun m => (π m).expectedDurationScore (B.directFiniteApproximation hZero m)
      (B.directScheduledCloudScore hZero (Ioi b) m)) atTop
      (𝓝 (∫ v, B.bandScore (Ioi b) v*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) := by
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (B.markCutoff_tendsto.eventually (gt_mem_nhds hb))
  let ret := fun m : ℕ => m+J
  let N := fun m => B.directVirtualCount hZero (m+J)
  let κ := fun m => (B.directVirtualOfferLaw hZero (m+J):Measure ℝ)
  let hκ := fun m => (B.directVirtualOfferLaw_bounds hZero (m+J)).mono (fun _ hx => hx.1)
  let Q := fun m => B.directVirtualOfferInstance hZero (m+J)
  let P := fun m => (B.individualPrefix (m+J)).appendIndependent (Q m)
  have hShift : Tendsto ret atTop atTop := tendsto_add_atTop_nat J
  have hCap (m) : ∀ᵐ x ∂κ m, x≤(B.cap:ℝ) := (B.directVirtualOfferLaw_bounds hZero (m+J)).mono (fun _ hx => hx.2)
  have hCapP (m) : ∀ i, ∀ᵐ x ∂(P m).law i, x≤(B.cap:ℝ) :=
    (B.individualPrefix (m+J)).appendIndependent_bounded (Q m)
      (fun i => (B.individual_supported i.val).mono (fun _ hx => hx.2)) (fun _ => hCap m)
  let hP := fun m => (P m).integrable_maximum_of_bounded (hCapP m)
  let π := fun m => (P m).valuePolicy (hP m) hw.le hc.le
  have hTail : ∀ m d, 0<d → (P m).tailCount d≤(B.totalTailMass d).toReal := by
    intro m d hd
    have h := B.directFiniteApproximation_tailCount_le hZero (m+J) hd
    rw [B.directFiniteApproximation_eq_appendVirtual hZero (m+J)] at h
    exact h
  have hV : Tendsto (fun m => ProphetSecretary.Model.optimalScalarValue (P m) w c) atTop (𝓝 (B.optimalScalarValue w c)) := by
    have h := (B.directFiniteApproximation_value_tendsto hZero hw.le hc.le).comp hShift
    simp_rw [B.directFiniteApproximation_eq_appendVirtual hZero] at h
    exact h
  have hNCast : Tendsto (fun m => (N m:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((B.directVirtualCount_tendsto hZero).comp hShift)
  have hp (m) : (κ m).real (Ioi b)=B.intensity.real (Ioi b)/(N m:ℝ) :=
    B.directVirtualOfferLaw_upper_mass_of_cutoff_le hZero (m+J) hb (hJ (m+J) (Nat.le_add_left J m)).le
  have hLim := B.direct_canonical_cloud_score_limits hZero ret N hShift
    (fun m => B.directVirtualCount_positive hZero (m+J)) hNCast κ hκ hCap
    (fun d hd => (B.directVirtualOfferLaw_threshold_tendsto hZero d hd).comp hShift)
    (fun d hd => (B.directVirtualOfferLaw_square_sum_tendsto hZero d hd.le).comp hShift)
    (fun d => (B.totalTailMass d).toReal) (fun _ _ => ENNReal.toReal_nonneg) hTail b
    (B.terminal.property.trans_lt hb) hAtom (fun m => B.directVirtualOfferLaw_zero_mass_ge_half hZero (m+J)) hp hw hc hNorm hV
  have hEqual (m) := canonical_scores_congr_instance (B.directFiniteApproximation_eq_appendVirtual hZero (m+J))
    ((B.directFiniteApproximation hZero (m+J)).integrable_maximum_of_bounded (B.directFiniteApproximation_bounded hZero (m+J)))
    (hP m) hw.le hc.le (B.directScheduledCloudScore hZero (Ioi b) (m+J))
  constructor
  · apply (tendsto_add_atTop_iff_nat J).mp
    exact hLim.1.congr (fun m => (hEqual m).1.symm)
  · apply (tendsto_add_atTop_iff_nat J).mp
    exact hLim.2.congr (fun m => (hEqual m).2.symm)
end ProphetSecretary.Limiting.CountableInstance
