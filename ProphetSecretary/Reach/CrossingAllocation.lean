import ProphetSecretary.Reach.SurvivalAllocation
import ProphetSecretary.Model.CrossingRoots

/-!
# Survival allocation at a deterministic continuation root

For a fixed unseen state and candidate value, the crossing root is deterministic.
The remaining-horizon child coefficient is exactly its root coefficient, which
is independent of the global scalar duration weight.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Instance.survival_allocation_at_crossing (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A)
    {z x K : ℝ} (hz : 0 < z)
    (hx : optimalScalarValue (P.restrictTo A) 1 0 < x)
    (hroot : (P.restrictTo A).durationRoot (P.restrictTo_integrable_maximum A hP) x < z)
    (W : Seed × History n → ℝ) (hW : Measurable W) (hWbounds : ∀ y, 0 ≤ W y ∧ W y ≤ K) :
    let Q := P.restrictTo A
    let hQ := P.restrictTo_integrable_maximum A hP
    let t := Q.crossingTime hQ z x
    let π := (P.valuePolicy hP zero_le_one hz.le).rule.withAuxiliarySeed (Seed := Seed)
    let ψ := Q.valuePolicy hQ zero_le_one (Q.durationRoot_nonnegative hQ x)
    let G := prefixSurvivalWeight π W i t
    (1 - t) * ψ.expectedDuration Q *
      (∫ ω in {ω : World n Seed | otherUnseen ω.2.1 i t = A}, G ω ∂P.worldLaw ν) ≤
      ∫ ω in {ω : World n Seed | otherUnseen ω.2.1 i t = A}, G ω *
        (∫ s in Icc t (1 : ℝ), (if s ≤ π.pendingTime ω.2.2 ω.1 ω.2.1 i then (1 : ℝ) else 0)) ∂P.worldLaw ν := by
  let Q := P.restrictTo A
  let hQ := P.restrictTo_integrable_maximum A hP
  let t := Q.crossingTime hQ z x
  have ht := Q.crossingTime_mem_Ioo hQ hz hx hroot
  have ha : z * (1 - t) = Q.durationRoot hQ x := by
    dsimp [t, Instance.crossingTime]
    rw [sub_sub_cancel, ← mul_div_assoc, mul_div_cancel_left₀ _ hz.ne']
  have h := P.survival_allocation_integral hP ν A i hAi zero_lt_one hz.le ht.1 ht.2 W hW hWbounds
  change z * (1 - Q.crossingTime hQ z x) = Q.durationRoot hQ x at ha
  simpa only [ha] using h

end ProphetSecretary.Model
