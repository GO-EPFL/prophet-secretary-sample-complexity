import ProphetSecretary.Limiting.FiniteBodyOperations
import ProphetSecretary.Limiting.NoReserve

/-!
# Finite original-sequence closure, paper `lem:closure`

Every consecutive finite sequence is specified by the operation relation.
The original sequence is an explicit input, and residual schedules are chosen
from its current structural limits. Actual value and maximum convergence
are derived after the finite trace is constructed.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
universe uClosure
namespace ProphetSecretary.Limiting

lemma BodyModification.lift_finite_given_sequence {A : FiniteBodySequence} {B : CountableInstance}
    (h : Relation.ReflTransGen BodyModification.{uClosure} A.target B) (hA : A.Converges) :
    ∃ D : FiniteBodySequence, D.target=B ∧
      Relation.ReflTransGen FiniteSequenceModification.{uClosure} A D ∧ D.Converges := by
  induction h with
  | refl => exact ⟨A,rfl,Relation.ReflTransGen.refl,hA⟩
  | @tail B C _hPrevious hLast ih =>
    obtain ⟨D,hD,hTrace,hConverges⟩ := ih
    have hLast' : BodyModification.{uClosure} D.target C := by rw [hD]; exact hLast
    obtain ⟨E,hE,hStep,hEConverges⟩ := hLast'.lift_given_sequence hConverges
    exact ⟨E,hE,hTrace.tail hStep,hEConverges⟩

/-- Paper `lem:closure`: a finite operation plan has an actual consecutive finite-product trace
starting at the specified original sequence, with actual V/M convergence. -/
theorem closure_of_finite_body_modifications (sizes : ℕ → ℕ)
    (P : ∀ m, Model.Instance (sizes m)) (B : CountableInstance)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ))
    (h : LabeledBandConvergence sizes P B) {D : CountableInstance}
    (hPlan : Relation.ReflTransGen BodyModification.{uClosure} B D) :
    ∃ A : FiniteBodySequence, A.target=D ∧
      Relation.ReflTransGen FiniteSequenceModification.{uClosure} (FiniteBodySequence.ofSequence sizes P B hCap) A ∧
      A.Converges ∧ Tendsto (fun m => (A.offers m).expectedMaximum) atTop (𝓝 D.expectedMaximum) ∧
      (∀ W C : ℝ≥0, ∀ ε>(0 : ℝ), ∀ᶠ m in atTop, ∀ w c : ℝ,
        0≤w → w≤W → 0≤c → c≤C → |Model.optimalScalarValue (A.offers m) w c-D.optimalScalarValue w c|<ε) ∧
      ∀ w c : ℝ, 0≤w → 0≤c → ProphetSecretary.Model.optimalCompetitiveRatio*(w*D.expectedMaximum+c)≤D.optimalScalarValue w c := by
  let A := FiniteBodySequence.ofSequence sizes P B hCap
  have hA : A.Converges := h
  have hPlan' : Relation.ReflTransGen BodyModification.{uClosure} A.target D := hPlan
  obtain ⟨A',hTarget,hTrace,hConverges⟩ := BodyModification.lift_finite_given_sequence hPlan' hA
  have hConv : LabeledBandConvergence A'.size A'.offers A'.target := hConverges
  refine ⟨A',hTarget,hTrace,hConverges,?_,?_,?_⟩
  · have hMax := hConv.expectedMaximum_tendsto A'.bounded
    simpa only [hTarget] using hMax
  · intro W C ε hε
    filter_upwards [hConv.values_and_maxima A'.bounded W C ε hε] with m hm
    simpa only [hTarget] using hm.1
  · intro w c hw hc
    exact D.globalScalar_inequality hw hc

end ProphetSecretary.Limiting
