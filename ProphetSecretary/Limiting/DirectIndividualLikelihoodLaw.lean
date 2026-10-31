import ProphetSecretary.Limiting.DirectIndividualScore
import ProphetSecretary.Limiting.CountableIndividualTilt
import ProphetSecretary.Probability.WideLikelihoodPath

/-!
# The exact retained-individual likelihood family in direct arrays

Only the retained copy of the designated individual changes law. All virtual
offers and every other individual remain unchanged, and the same virtual
count is used throughout the parameter interval. When that individual is not
yet retained, the score and the finite family are identically unchanged.
-/

open MeasureTheory Set BoundedContinuousFunction
open scoped Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model ProphetSecretary.Probability CountableInstance

private lemma tiltLaw_zero_score (μ : Measure ℝ) (θ : ℝ) : tiltLaw μ (fun _ => 0) θ=μ := by
  simp only [tiltLaw,tiltFactor,mul_zero,add_zero,ENNReal.ofReal_one]
  exact withDensity_one

theorem directIndividualScore_likelihoodWidePath (B : CountableInstance) (ret N : ℕ)
    (Q : Model.Instance N) (i : ℕ) (f : ℝ →ᵇ ℝ) {θ : ℝ} (hθ : |θ|≤1/4) :
    ((B.individualPrefix ret).appendIndependent Q).likelihoodWidePath
      (directIndividualScore (B.individualPrefix ret) Q i f)
      (directIndividualScore_properties (B.individualPrefix ret) Q i f).1
      (fun j => Filter.Eventually.of_forall ((directIndividualScore_properties (B.individualPrefix ret) Q i f).2.1 j))
      (directIndividualScore_properties (B.individualPrefix ret) Q i f).2.2.1 θ=
      ((B.individualLikelihoodPath i (centeredBoundedScore (B.individuals i : Measure ℝ) f)
        (continuous_centeredBoundedScore (B.individuals i : Measure ℝ) f).measurable
        (Filter.Eventually.of_forall (centeredBoundedScore_abs_le_one (B.individuals i : Measure ℝ) f))
        (centeredBoundedScore_mean (B.individuals i : Measure ℝ) f) θ).individualPrefix ret).appendIndependent Q := by
  let h := directIndividualScore (B.individualPrefix ret) Q i f
  let hh := (directIndividualScore_properties (B.individualPrefix ret) Q i f).1
  let hb : ∀ j, ∀ᵐ x ∂((B.individualPrefix ret).appendIndependent Q).law j, |h j x|≤1 :=
    fun j => Filter.Eventually.of_forall ((directIndividualScore_properties (B.individualPrefix ret) Q i f).2.1 j)
  let hm := (directIndividualScore_properties (B.individualPrefix ret) Q i f).2.2.1
  change ((B.individualPrefix ret).appendIndependent Q).likelihoodWidePath h hh hb hm θ=_
  rw [Model.Instance.likelihoodWidePath_of_mem _ h hh hb hm (hθ.trans (by norm_num)),
    B.individualLikelihoodPath_of_mem i (centeredBoundedScore (B.individuals i : Measure ℝ) f)
      (continuous_centeredBoundedScore (B.individuals i : Measure ℝ) f).measurable
      (Filter.Eventually.of_forall (centeredBoundedScore_abs_le_one (B.individuals i : Measure ℝ) f))
      (centeredBoundedScore_mean (B.individuals i : Measure ℝ) f) hθ]
  apply Model.Instance.ext_law
  funext j
  induction j using Fin.addCases with
  | left j =>
    change tiltLaw (((B.individualPrefix ret).appendIndependent Q).law (j.castAdd N)) (h (j.castAdd N)) θ=_
    rw [Model.Instance.appendIndependent_law_left,Model.Instance.appendIndependent_law_left]
    by_cases hi : i<ret
    · have hActive : ((B.individualPrefix ret).appendIndependent Q).law ((⟨i,hi⟩ : Fin ret).castAdd N)=
          (B.individuals i : Measure ℝ) := by
        rw [Model.Instance.appendIndependent_law_left]
        rfl
      by_cases hji : j.val=i
      · have hj : j=⟨i,hi⟩ := Fin.ext hji
        subst j
        have hSc : h ((⟨i,hi⟩ : Fin ret).castAdd N)=centeredBoundedScore (B.individuals i : Measure ℝ) f := by
          funext x
          simp only [h,directIndividualScore,dif_pos hi,individualContinuousScore,singleScore,if_true,hActive]
        rw [hSc]
        change tiltLaw (B.individuals i : Measure ℝ) (centeredBoundedScore (B.individuals i : Measure ℝ) f) θ=
          (Function.update B.individuals i _ i : Measure ℝ)
        rw [Function.update_self]
        rfl
      · have hj : j.castAdd N≠(⟨i,hi⟩ : Fin ret).castAdd N := by
          intro he
          apply hji
          exact congrArg Fin.val he
        have hSc : h (j.castAdd N)=(fun _ => 0) := by
          funext x
          simp only [h,directIndividualScore,dif_pos hi,individualContinuousScore,singleScore,if_neg hj]
        rw [hSc,tiltLaw_zero_score]
        change (B.individuals j.val : Measure ℝ)=(Function.update B.individuals i _ j.val : Measure ℝ)
        rw [Function.update_of_ne hji]
    · simp only [h,directIndividualScore,dif_neg hi]
      rw [tiltLaw_zero_score]
      have hj : j.val≠i := fun he => hi (he ▸ j.isLt)
      change (B.individuals j.val : Measure ℝ)=(Function.update B.individuals i _ j.val : Measure ℝ)
      rw [Function.update_of_ne hj]
  | right j =>
    change tiltLaw (((B.individualPrefix ret).appendIndependent Q).law (j.natAdd ret)) (h (j.natAdd ret)) θ=_
    rw [Model.Instance.appendIndependent_law_right]
    by_cases hi : i<ret
    · have hj : j.natAdd ret≠(⟨i,hi⟩ : Fin ret).castAdd N := by
        intro he
        have hVal := congrArg Fin.val he
        simp only [Fin.val_natAdd,Fin.val_castAdd] at hVal
        omega
      have hSc : h (j.natAdd ret)=(fun _ => 0) := by
        funext x
        simp only [h,directIndividualScore,dif_pos hi,individualContinuousScore,singleScore,if_neg hj]
      rw [hSc,tiltLaw_zero_score,Model.Instance.appendIndependent_law_right]
    · simp only [h,directIndividualScore,dif_neg hi]
      rw [tiltLaw_zero_score,Model.Instance.appendIndependent_law_right]

end ProphetSecretary.Limiting
