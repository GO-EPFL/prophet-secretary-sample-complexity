import ProphetSecretary.Limiting.OriginalIndividualScoreLift
import ProphetSecretary.Limiting.OriginalCloudScoreLift
import ProphetSecretary.Limiting.ScoreLiftRegularity

/-!
# Complete likelihood-score lifting on the original finite sequence

These are the two cases of `updual:scorelift`: an individual continuous bounded
score after the fixed scaling 2(‖f‖+1), and the centered complete count in an
upper positive Poisson continuity band. The actual original-coordinate scores
have the stated global bounds and explicit dimension-independent information
bounds. The same witnesses satisfy all quarter-interval density, cap, Fisher,
first-moment, optimized-value, fixed-policy and benchmark regularity clauses.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

theorem OrderedBandConvergence.original_individual_score_lift_complete
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (hZero : B.terminal=0)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap:ℝ))
    {S0 lam : ℝ} (hS0 : 0≤S0) (hS : ∀ m, (P m).totalFirstMoment≤S0)
    (hlam : lam∈Ioo (0:ℝ) 1) (lams : ℕ → ℝ) (hRange : ∀ m, lams m∈Icc (0:ℝ) 1)
    (hLam : Tendsto lams atTop (𝓝 lam))
    (hV : Tendsto (fun m => Model.optimalScalarValue (P m) (lams m) (1-lams m)) atTop
      (𝓝 (B.optimalScalarValue lam (1-lam)))) (i : ℕ) (f : ℝ →ᵇ ℝ) :
    ∃ (δ : ℝ) (score : ∀ m, Fin (sizes m) → ℝ → ℝ)
      (hh : ∀ m j, Measurable (score m j))
      (hbScore : ∀ m j, ∀ᵐ x ∂(P m).law j, |score m j x|≤1)
      (hm : ∀ m j, (∫ x, score m j x ∂(P m).law j)=0),
      0<δ ∧ (∀ m j x, |score m j x|≤1) ∧
      (∀ m, information (P m).law (score m)≤1) ∧
      (let ρ := fun m => (P m).unitCanonicalPolicy ((P m).integrable_maximum_of_bounded (hCap m))
        (lams m) (hRange m)
      Tendsto (fun m => (ρ m).expectedRewardScore (P m) (score m)) atTop
        (𝓝 (∫ v, centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 i)*
          (B.valueRule lam (1-lam)).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
      Tendsto (fun m => (ρ m).expectedDurationScore (P m) (score m)) atTop
        (𝓝 (∫ v, centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 i)*
          (B.valueRule lam (1-lam)).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ())))) ∧
      UniformLikelihoodRegularity sizes P
        (fun m θ => (P m).likelihoodWidePath (score m) (hh m) (hbScore m) (hm m) θ)
        score lams B.cap S0 (1) δ := by
  obtain ⟨δ,ls,score,hδ,hLs,_hEq,hOff,hProps,hCov⟩ :=
    h.original_individual_score_lift hZero hCap hS0 hS hlam lams hRange hLam hV i f
  let hh := fun m => (hProps m).1
  let hbScore : ∀ m j, ∀ᵐ x ∂(P m).law j, |score m j x|≤1 :=
    fun m j => Filter.Eventually.of_forall ((hProps m).2.1 j)
  let hm := fun m => (hProps m).2.2.1
  have hInfo (m) := (hProps m).2.2.2
  refine ⟨δ,score,hh,hbScore,hm,hδ,(fun m => (hProps m).2.1),hInfo,hCov,?_⟩
  exact score_lift_uniform_regularity sizes P B.cap.property hS0 zero_le_one hδ hCap hS
    score hh hbScore hm hInfo ls lams hLs hOff

theorem OrderedBandConvergence.original_upperBand_score_lift_complete
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (hZero : B.terminal=0)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap:ℝ))
    {S0 lam : ℝ} (hS0 : 0≤S0) (hS : ∀ m, (P m).totalFirstMoment≤S0)
    (hlam : lam∈Ioo (0:ℝ) 1) (lams : ℕ → ℝ) (hRange : ∀ m, lams m∈Icc (0:ℝ) 1)
    (hLam : Tendsto lams atTop (𝓝 lam))
    (hV : Tendsto (fun m => Model.optimalScalarValue (P m) (lams m) (1-lams m)) atTop
      (𝓝 (B.optimalScalarValue lam (1-lam)))) (b : ℝ) (hb : 0<b) (hAtom : B.intensity {b}=0) :
    ∃ (δ : ℝ) (score : ∀ m, Fin (sizes m) → ℝ → ℝ)
      (hh : ∀ m j, Measurable (score m j))
      (hbScore : ∀ m j, ∀ᵐ x ∂(P m).law j, |score m j x|≤1)
      (hm : ∀ m j, (∫ x, score m j x ∂(P m).law j)=0),
      0<δ ∧ (∀ m j x, |score m j x|≤1) ∧
      (∀ m, information (P m).law (score m)≤2*S0/b) ∧
      (let ρ := fun m => (P m).unitCanonicalPolicy ((P m).integrable_maximum_of_bounded (hCap m))
        (lams m) (hRange m)
      Tendsto (fun m => (ρ m).expectedRewardScore (P m) (score m)) atTop
        (𝓝 (∫ v, B.bandScore (Ioc b (B.cap:ℝ)) v*
          (B.valueRule lam (1-lam)).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
      Tendsto (fun m => (ρ m).expectedDurationScore (P m) (score m)) atTop
        (𝓝 (∫ v, B.bandScore (Ioc b (B.cap:ℝ)) v*
          (B.valueRule lam (1-lam)).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ())))) ∧
      UniformLikelihoodRegularity sizes P
        (fun m θ => (P m).likelihoodWidePath (score m) (hh m) (hbScore m) (hm m) θ)
        score lams B.cap S0 (2*S0/b) δ := by
  obtain ⟨δ,ls,score,hδ,hLs,_hEq,hOff,hProps,hCov⟩ :=
    h.original_upperBand_score_lift hZero hCap hS0 hS hlam lams hRange hLam hV b hb hAtom
  let hh := fun m => (hProps m).1
  let hbScore : ∀ m j, ∀ᵐ x ∂(P m).law j, |score m j x|≤1 :=
    fun m j => Filter.Eventually.of_forall ((hProps m).2.1 j)
  let hm := fun m => (hProps m).2.2.1
  have hInfo (m) := (hProps m).2.2.2
  refine ⟨δ,score,hh,hbScore,hm,hδ,(fun m => (hProps m).2.1),hInfo,hCov,?_⟩
  exact score_lift_uniform_regularity sizes P B.cap.property hS0 (by positivity : 0≤2*S0/b) hδ hCap hS
    score hh hbScore hm hInfo ls lams hLs hOff
end ProphetSecretary.Limiting
