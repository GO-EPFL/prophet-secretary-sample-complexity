import ProphetSecretary.Limiting.HybridPositiveBand
import ProphetSecretary.Limiting.Campbell

/-!
# Anonymous-candidate hybrid acceptance bands

The intensity of a positive near-boundary band is bounded by its clock width
and its mark tail mass. The complete Poisson configuration is analytical;
the actual threshold depends only on retained identities and elapsed time.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def FiniteIntensityHybridInstance.anonymousPositiveBand (B : FiniteIntensityHybridInstance n)
    (w c b e : ℝ) (u : Fin n → ℝ) : Set Point :=
  {p | b ≤ p.2 ∧ |B.candidateGap w c none p.2 u p.1| ≤ e}

lemma FiniteIntensityHybridInstance.measurableSet_anonymousPositiveBand (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (b e : ℝ) (u : Fin n → ℝ) :
    MeasurableSet (B.anonymousPositiveBand w c b e u) := by
  have hm : Measurable (fun p : Point => (p.2,(u,p.1))) := by fun_prop
  have hg := (B.measurable_candidateGap_joint hw hc none).comp hm
  exact (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_le (continuous_abs.measurable.comp hg) measurable_const)

theorem FiniteIntensityHybridInstance.anonymousPositiveBand_intensity
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {H w c b L e : ℝ}
    (hH : 0 ≤ H) (hCap : (B.cap : ℝ) ≤ H) (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    (hL : B.tailCount (b/4) ≤ L) (he0 : 0 ≤ e) (he : e ≤ w*b/4) (u : Fin n → ℝ) :
    ProphetSecretary.Limiting.intensity B.intensity (B.anonymousPositiveBand w c b e u) ≤
      ENNReal.ofReal (2*e/(c*Model.positiveBandDuration H w c b L)) *
        (B.intensity : Measure ℝ) (Ici b) := by
  let K := 2*e/(c*Model.positiveBandDuration H w c b L)
  have hK : 0 ≤ K := by
    have := Model.positiveBandDuration_pos hH hw hc hb ((B.tailCount_nonnegative _).trans hL)
    dsimp only [K]
    positivity
  have hS := B.measurableSet_anonymousPositiveBand hw.le hc.le b e u
  have hSlice (x : ℝ) :
      Model.Instance.uniformClock ((fun t => (t,x)) ⁻¹' B.anonymousPositiveBand w c b e u) ≤
        (Ici b).indicator (fun _ => ENNReal.ofReal K) x := by
    by_cases hx : b ≤ x
    · rw [Set.indicator_of_mem (show x ∈ Ici b from hx)]
      have hm : MeasurableSet {t | |B.candidateGap w c none x u t| ≤ e} :=
        measurableSet_le (continuous_abs.measurable.comp (B.measurable_candidateGap hw.le hc.le none x u)) measurable_const
      have hEq : ((fun t => (t,x)) ⁻¹' B.anonymousPositiveBand w c b e u) =
          {t | |B.candidateGap w c none x u t| ≤ e} := by
        ext t
        simp only [anonymousPositiveBand,mem_preimage,mem_setOf_eq,hx,true_and]
      rw [hEq,Model.Instance.uniformClock,Measure.restrict_apply hm,inter_comm]
      exact B.candidateGap_positiveBand_volume ha hH hCap hw hc hb hL he none hx u
    · rw [Set.indicator_of_notMem (show x ∉ Ici b from hx)]
      have hEq : ((fun t => (t,x)) ⁻¹' B.anonymousPositiveBand w c b e u) = ∅ := by
        ext t
        simp only [anonymousPositiveBand,mem_preimage,mem_setOf_eq,hx,false_and,mem_empty_iff_false]
      rw [hEq,measure_empty]
  change (Model.Instance.uniformClock.prod (B.intensity : Measure ℝ)) _ ≤ _
  rw [Measure.prod_apply_symm hS]
  calc
    _ ≤ ∫⁻ x, (Ici b).indicator (fun _ => ENNReal.ofReal K) x ∂(B.intensity : Measure ℝ) := lintegral_mono hSlice
    _ = _ := lintegral_indicator_const measurableSet_Ici _

/-- Campbell's formula turns the intensity estimate into an expected number
of all anonymous candidates near the boundary, without a stopping condition. -/
theorem FiniteIntensityHybridInstance.anonymousPositiveBand_expected_count
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {H w c b L e : ℝ}
    (hH : 0 ≤ H) (hCap : (B.cap : ℝ) ≤ H) (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    (hL : B.tailCount (b/4) ≤ L) (he0 : 0 ≤ e) (he : e ≤ w*b/4) (u : Fin n → ℝ) :
    (∫⁻ ω, countingMeasure ω (B.anonymousPositiveBand w c b e u) ∂configurationLaw B.intensity) ≤
      ENNReal.ofReal (2*e/(c*Model.positiveBandDuration H w c b L)) *
        (B.intensity : Measure ℝ) (Ici b) := by
  rw [expected_count B.intensity (B.measurableSet_anonymousPositiveBand hw.le hc.le b e u)]
  exact B.anonymousPositiveBand_intensity ha hH hCap hw hc hb hL he0 he u

end ProphetSecretary.Limiting
