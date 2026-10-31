import ProphetSecretary.Limiting.ScalarDiameterCriticalCountersequence
import ProphetSecretary.Limiting.CountableLiftableDurationScore
import ProphetSecretary.Limiting.OriginalIndividualScoreLimit
import ProphetSecretary.Limiting.OriginalCloudScoreLimit
import ProphetSecretary.Model.ScalarValueWeightLimit
import ProphetSecretary.Model.ScalarDiameterScoreContradiction
import ProphetSecretary.Model.ScalarDiameterBoundary

/-!
# The uniform quadratic diameter of scalar critical sublevels

A failure on an interior weight interval gives a critical ordered limit.
Nondegeneracy supplies one of the two actual likelihood-score directions;
original-instance score transfer preserves its nonzero duration response.
The proved finite curvature inequality contradicts the countersequence.
Uniform endpoint slack extends the result to every normalized weight.
Paper correspondence: `updual:modulus` and `updual:diameter`.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical NNReal Topology
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model ProphetSecretary.Probability CountableInstance

theorem bounded_interior_scalarGap_quadratic_diameter (H : ℝ≥0) (S0 mu δ : ℝ)
    (hS0 : 0≤S0) (hmu : 0<mu) (hδ : 0<δ) :
    ∃ K : ℝ, 0≤K ∧ ∀ (n : ℕ) (P : Instance n), (∀ i, ∀ᵐ x ∂P.law i, x≤(H : ℝ)) →
      P.totalFirstMoment≤S0 → mu≤P.expectedMaximum → ∀ a b : ℝ,
      a∈Icc δ (1-δ) → b∈Icc δ (1-δ) →
      (b-a)^2≤K*(normalizedScalarGap P a+normalizedScalarGap P b) := by
  by_contra hNo
  have hFail : ∀ K : ℝ, 0≤K → ∃ (n : ℕ) (P : Instance n) (a b : ℝ),
      (∀ i, ∀ᵐ x ∂P.law i, x≤(H : ℝ)) ∧ P.totalFirstMoment≤S0 ∧ mu≤P.expectedMaximum ∧
      a∈Icc δ (1-δ) ∧ b∈Icc δ (1-δ) ∧
      K*(normalizedScalarGap P a+normalizedScalarGap P b)<(b-a)^2 := by
    intro K hK
    by_contra hNoWitness
    apply hNo
    refine ⟨K,hK,?_⟩
    intro n P hcap hS hMean a b ha hb
    by_contra hIneq
    exact hNoWitness ⟨n,P,a,b,hcap,hS,hMean,ha,hb,lt_of_not_ge hIneq⟩
  obtain ⟨sizes,P,a,b,l,B,wgt,hcap,hS,_hMean,hA,hB,hRatio,hl,hCap,hZero,_hMB,hCritical,hBands,hLam,hM,hUniform⟩ :=
    exists_critical_scalarDiameter_countersequence H S0 mu δ hmu hδ hFail
  have hCapB (m : ℕ) (i : Fin (sizes m)) : ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ) := by
    simpa only [hCap] using hcap m i
  let lams := fun m => (a m+b m)/2
  have hRange (m : ℕ) : lams m∈Icc δ (1-δ) := by
    dsimp only [lams]
    constructor <;> linarith only [(hA m).1,(hA m).2,(hB m).1,(hB m).2]
  have hRangeUnit (m : ℕ) : lams m∈Icc (0 : ℝ) 1 :=
    ⟨hδ.le.trans (hRange m).1,by linarith only [(hRange m).2,hδ]⟩
  have hlInterior : l∈Ioo (0 : ℝ) 1 := by constructor <;> linarith only [hl.1,hl.2,hδ]
  have hFixed : Tendsto (fun m => optimalScalarValue (P m) l (1-l)) atTop
      (𝓝 (B.optimalScalarValue l (1-l))) := by
    have hNonneg : ∀ z∈({(l,1-l)} : Set (ℝ × ℝ)), 0≤z.1 ∧ 0≤z.2 := by
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact ⟨hlInterior.1.le,sub_nonneg.mpr hlInterior.2.le⟩
    exact (hUniform {(l,1-l)} isCompact_singleton hNonneg).tendsto_at (Set.mem_singleton _)
  have hV := optimalScalarValue_tendsto_along_weights sizes P B.cap.property hCapB lams hRangeUnit
    ⟨hlInterior.1.le,hlInterior.2.le⟩ hLam hFixed
  let ρ := fun m => (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCapB m))
    (hδ.le.trans (hRange m).1) (show 0≤1-lams m from by linarith only [(hRange m).2,hδ.le])
  have hOpt (m : ℕ) : (ρ m).scalarObjective (P m) ((a m+b m)/2) (1-(a m+b m)/2)=
      optimalScalarValue (P m) ((a m+b m)/2) (1-(a m+b m)/2) := by
    exact (P m).valuePolicy_optimal ((P m).integrable_maximum_of_bounded (hCapB m))
      (hδ.trans_le (hRange m).1) (by linarith only [(hRange m).2,hδ.le])
  rcases B.exists_liftable_negative_duration_score hlInterior.1 (sub_pos.mpr hlInterior.2) hCritical with hI|hCloud
  · obtain ⟨i,f,hNegative⟩ := hI
    have hLimits := hBands.original_individual_score_limits hZero hCapB hS0 hS hδ hlInterior
      lams hRange hLam hV i f
    have hProps (m : ℕ) := weightedIndividualScore_properties (P m) wgt i f
    exact scalarDiameter_countersequence_impossible_of_durationScore_limit sizes P B.cap.property hS0 hδ zero_le_one
      hCapB hS a b hA hB ρ hOpt (fun m => weightedIndividualScore (P m) wgt i f)
      (fun m => (hProps m).1) (fun m j => Eventually.of_forall ((hProps m).2.1 j))
      (fun m => (hProps m).2.2.1) (fun m => (hProps m).2.2.2) hRatio (ne_of_lt hNegative) hLimits.2
  · obtain ⟨d,hd,hAtom,hNegative⟩ := hCloud
    obtain ⟨Ns,_hNs,hProps,hLimits⟩ := hBands.original_upperBand_score_limits hZero hCapB hS0 hS hδ
      hlInterior lams hRange hLam hV d hd hAtom
    have hI0 : 0≤2*S0/d := div_nonneg (mul_nonneg (by norm_num) hS0) hd.le
    exact scalarDiameter_countersequence_impossible_of_durationScore_limit sizes P B.cap.property hS0 hδ hI0
      hCapB hS a b hA hB ρ hOpt (fun m => weightedResidualScore (P m) wgt (Ns m) (Ioi d))
      (fun m => (hProps m).1) (fun m j => Eventually.of_forall ((hProps m).2.1 j))
      (fun m => (hProps m).2.2.1) (fun m => (hProps m).2.2.2) hRatio (ne_of_lt hNegative) hLimits.2

/-- `updual:modulus`. The constant is fixed before the finite size, instance,
and the two weights; its dependence is only on H, S0, mu and the global C_PS. -/
theorem bounded_scalarGap_quadratic_diameter (H : ℝ≥0) (S0 mu : ℝ)
    (hS0 : 0<S0) (hmu : 0<mu) :
    ∃ K : ℝ, 0<K ∧ ∀ (n : ℕ) (P : Instance n), (∀ i, ∀ᵐ x ∂P.law i, x≤(H : ℝ)) →
      P.totalFirstMoment≤S0 → mu≤P.expectedMaximum → ∀ a b : ℝ,
      a∈Icc (0 : ℝ) 1 → b∈Icc (0 : ℝ) 1 →
      (b-a)^2≤K*(normalizedScalarGap P a+normalizedScalarGap P b) := by
  obtain ⟨δ,hδ,hExtend⟩ := scalarDiameter_interior_to_global H S0 mu hmu
  obtain ⟨K,hK,hInterior⟩ := bounded_interior_scalarGap_quadratic_diameter H S0 mu δ hS0.le hmu hδ.1
  exact hExtend K hK hInterior

end ProphetSecretary.Limiting
