import ProphetSecretary.Limiting.DirectCloudTargetLimit

/-!
# The concrete Poisson-band alternative of the critical experiment

A negative upper-band complete-count duration response determines one
actual reversed-score family. One finite shift simultaneously enforces mean
normalization, interior weights and a uniformly negative target coefficient.
Every elementary property is proved from the constructed direct arrays.
The information, Taylor and statistical reduction are applied separately.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

theorem exists_cloud_critical_likelihood_family (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {w c : ℝ} (hw : 0<w) (hc : 0<c) (hSum : w+c=1)
    (hCritical : B.IsCritical w c) (hQuarterW : 1/4≤w) (hQuarterC : 1/4≤c)
    (level : ℝ) (hLevel : (B.terminal:ℝ)<level) (hAtom : B.intensity {level}=0)
    (hNegative : (∫ v : CompleteWorld Unit, B.bandScore (Ioi level) v*
      (B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))<0) :
    ∃ (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m)) (H δ I b : ℝ)
      (L : ℝ → ℝ) (lams : ℕ → ℝ) (score : ∀ m, Fin (sizes m) → ℝ → ℝ)
      (πopt : ∀ m, RandomizedPolicy (sizes m)),
      0≤H ∧ 0<δ ∧ δ<1/2 ∧ 0≤I ∧ 0<b ∧
      (∀ m j, ∀ᵐ x ∂(P m).law j, x≤H) ∧
      (∀ d, 0<d → 0≤L d) ∧
      (∀ m d, 0<d → (P m).tailCount d≤L d) ∧
      (∀ m, lams m∈Icc δ (1-δ)) ∧
      (∀ m, (P m).expectedMaximum=1) ∧
      Tendsto (fun m => normalizedScalarGap (P m) (lams m)) atTop (𝓝 (0 : ℝ)) ∧
      (∀ m j, Measurable (score m j)) ∧
      (∀ m j, ∀ᵐ x ∂(P m).law j, |score m j x|≤1) ∧
      (∀ m j, (∫ x, score m j x ∂(P m).law j)=0) ∧
      (∀ m, information (P m).law (score m)≤I) ∧
      (∀ m, (πopt m).scalarObjective (P m) (lams m) (1-lams m)=
        Model.optimalScalarValue (P m) (lams m) (1-lams m)) ∧
      (∀ m, (πopt m).targetScoreResponse (P m) (score m)≤ -b) := by
  let dT := ∫ v : CompleteWorld Unit, B.bandScore (Ioi level) v*
    (B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ())
  let a := dT/w
  have ha : a<0 := div_neg_of_neg_of_pos hNegative hw
  let b := -a/2
  have hb : 0<b := div_pos (neg_pos.mpr ha) (by norm_num)
  have hLimit := B.directCloudNormalizedTargetScore_tendsto hZero hMean hw hc hSum hCritical level hLevel hAtom
  have hNegativeLevel : a<a/2 := by linarith only [ha]
  have hEvent : ∀ᶠ n : ℕ in atTop, B.directCloudNormalizedTargetScore hZero hw hc level n≤ -b := by
    filter_upwards [hLimit.eventually (gt_mem_nhds hNegativeLevel)] with n hn
    change B.directCloudNormalizedTargetScore hZero hw hc level n≤ -(-a/2)
    linarith only [hn]
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp hEvent
  obtain ⟨Kcut,_hKcut⟩ := Filter.eventually_atTop.mp (B.markCutoff_tendsto.eventually (gt_mem_nhds hLevel))
  let J := max (B.directNormalizationStart hZero hMean) (max K Kcut)
  have hJ : B.directNormalizationStart hZero hMean≤J := le_max_left _ _
  let sizes := B.shiftedDirectSize hZero J
  let P := B.normalizedDirectBase hZero hMean hJ
  let lams := B.normalizedDirectRewardWeight hZero J w c
  let score := B.normalizedDirectCloudScore hZero J (Ioi level)
  let πopt := B.normalizedDirectCanonicalPolicy hZero J hw hc
  have hProps := fun m => B.normalizedDirectCloudScore_properties hZero hMean hJ measurableSet_Ioi hLevel (Subset.refl (Ioi level)) m
  refine ⟨sizes,P,2*(B.cap : ℝ),1/16,2*B.intensity.real (Ioi level),b,(fun d => (B.totalTailMass (d/2)).toReal),lams,score,πopt,
    mul_nonneg (by norm_num) B.cap.property,by norm_num,by norm_num,(by positivity : 0≤2*B.intensity.real (Ioi level)),hb,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact B.normalizedDirectBase_cap hZero hMean hJ
  · exact fun _ _ => ENNReal.toReal_nonneg
  · exact fun m _ hd => B.normalizedDirectBase_tailCount_le hZero hMean hJ m hd
  · exact B.normalizedDirectWeights_quarter hZero hMean hJ hw hc hSum hQuarterW hQuarterC
  · exact B.normalizedDirectBase_expectedMaximum hZero hMean hJ
  · exact B.normalizedDirectBase_gap_tendsto hZero hMean hJ hw hc hSum hCritical
  · exact fun m => (hProps m).1
  · exact fun m j => Filter.Eventually.of_forall ((hProps m).2.1 j)
  · exact fun m => (hProps m).2.2.1
  · exact fun m => (hProps m).2.2.2
  · exact B.normalizedDirectCanonicalPolicy_optimal hZero hMean hJ hw hc
  · intro m
    have hEq : (πopt m).targetScoreResponse (P m) (score m)=
        B.directCloudNormalizedTargetScore hZero hw hc level (m+J) := by rfl
    rw [hEq]
    apply hK
    dsimp only [J]
    omega

end ProphetSecretary.Limiting.CountableInstance
