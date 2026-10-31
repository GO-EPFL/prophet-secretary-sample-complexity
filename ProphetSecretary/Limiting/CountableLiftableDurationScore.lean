import ProphetSecretary.Limiting.CountableNonzeroScores
import ProphetSecretary.Limiting.CountableUpperBandResponse
import ProphetSecretary.Probability.CenteredBoundedScore

/-!
# Nonzero duration directions in the original-sequence score normalization

The bounded clipped value function supplies the individual direction. Its
centered score differs from the centered linear value score by one positive
fixed factor. The cloud direction is an upper common continuity band. These
are exactly the two score types transferred in `updual:scorelift`.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Probability

theorem exists_liftable_negative_duration_score (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) :
    (∃ (i : ℕ) (f : ℝ →ᵇ ℝ),
      (∫ v : CompleteWorld Unit, centeredBoundedScore (B.individuals i : Measure ℝ) f (v.2.1 i)*
        (B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))<0) ∨
    (∃ b : ℝ, 0<b ∧ B.intensity {b}=0 ∧
      (∫ v : CompleteWorld Unit, B.bandScore (Ioi b) v*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))<0) := by
  rcases B.exists_negative_duration_score_at_critical hw hc hCritical with hI|hP
  · obtain ⟨i,hNegative⟩ := hI
    let f := boundedOfferValue B.cap
    let A := (B.cap : ℝ)/boundedScoreScale f
    have hCap : 0<(B.cap : ℝ) := B.cap_pos_of_critical hCritical
    have hA : 0<A := div_pos hCap (boundedScoreScale_positive f)
    have hScore (x : ℝ) : centeredBoundedScore (B.individuals i : Measure ℝ) f x=
        A*centeredValueScore (B.individuals i : Measure ℝ) B.cap x := by
      dsimp only [centeredBoundedScore,centeredValueScore,centeredRangeScore,A,f]
      field_simp [hCap.ne']
    refine Or.inl ⟨i,f,?_⟩
    have hEq : (∫ v : CompleteWorld Unit,
        centeredBoundedScore (B.individuals i : Measure ℝ) f (v.2.1 i)*(B.valueRule w c).realizedDuration v
          ∂B.completeWorldLaw (Measure.dirac ()))=
        A*(∫ v : CompleteWorld Unit, centeredValueScore (B.individuals i : Measure ℝ) B.cap (v.2.1 i)*
          (B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ())) := by
      simp_rw [hScore,mul_assoc]
      exact integral_const_mul _ _
    rw [hEq]
    exact mul_neg_of_pos_of_neg hA hNegative
  · obtain ⟨S,hS,b,hb,hSub,hNegative⟩ := hP
    obtain ⟨d,hd,_hTerminal,hAtom,_hAtoms,hUpper,_hCapped⟩ :=
      B.exists_upperContinuityBand_durationScore_negative hw hc hS hb hSub (ne_of_lt hNegative)
    exact Or.inr ⟨d,hd,hAtom,by simpa only [mul_comm] using hUpper⟩

end ProphetSecretary.Limiting.CountableInstance
