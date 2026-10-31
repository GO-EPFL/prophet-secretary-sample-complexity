import ProphetSecretary.Limiting.CountableRemainingState
import ProphetSecretary.Limiting.CountableIndividualOmission

/-!
# Actual independent value laws under countable zero masks

The masked online product law is the pushforward of the original independent
values through coordinatewise masking. This is a law identity, not an assumed
independence or policy-simulation interface. Zero identities remain present.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting

def maskOffer (keep : Bool) (x : ℝ) : ℝ := if keep = true then x else 0

def maskIndividualValues (keep : IndividualMask) (x : ℕ → ℝ) : ℕ → ℝ := fun i => maskOffer (keep i) (x i)

lemma measurable_maskOffer (keep : Bool) : Measurable (maskOffer keep) := by
  change Measurable (fun x : ℝ => if keep = true then x else 0)
  by_cases hk : keep = true
  · simp only [if_pos hk]
    exact measurable_id
  · simp only [if_neg hk]
    exact measurable_const

lemma measurable_maskIndividualValues :
    Measurable (fun z : IndividualMask × (ℕ → ℝ) => maskIndividualValues z.1 z.2) := by
  apply measurable_pi_lambda
  intro i
  have hk : Measurable (fun z : IndividualMask × (ℕ → ℝ) => z.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hx : Measurable (fun z : IndividualMask × (ℕ → ℝ) => z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  exact Measurable.ite (hk (measurableSet_singleton true)) hx measurable_const

lemma maskedProbabilityLaw_eq_map (q : ProbabilityMeasure ℝ) (keep : Bool) :
    (maskedProbabilityLaw q keep : Measure ℝ) = (q : Measure ℝ).map (maskOffer keep) := by
  by_cases hk : keep = true
  · have he : maskOffer keep = (id : ℝ → ℝ) := by funext x; exact if_pos hk
    calc
      (maskedProbabilityLaw q keep : Measure ℝ) = (q : Measure ℝ) := congrArg (fun p : ProbabilityMeasure ℝ => (p : Measure ℝ)) (if_pos hk)
      _ = (q : Measure ℝ).map (maskOffer keep) := by rw [he,Measure.map_id]
  · have he : maskOffer keep = (fun _ : ℝ => (0 : ℝ)) := by funext x; exact if_neg hk
    calc
      (maskedProbabilityLaw q keep : Measure ℝ) = Measure.dirac 0 := congrArg (fun p : ProbabilityMeasure ℝ => (p : Measure ℝ)) (if_neg hk)
      _ = (q : Measure ℝ).map (maskOffer keep) := by rw [he]; simp

lemma CountableInstance.maskValues_measurePreserving (B : CountableInstance) (keep : IndividualMask) :
    MeasurePreserving (maskIndividualValues keep) B.individualValuesLaw (B.maskIndividuals keep).individualValuesLaw := by
  have hm : Measurable (maskIndividualValues keep) :=
    measurable_maskIndividualValues.comp (measurable_const.prodMk measurable_id)
  refine ⟨hm,?_⟩
  have he := Measure.infinitePi_map_pi (μ := fun i => (B.individuals i : Measure ℝ))
    (f := fun i => maskOffer (keep i)) (fun i => measurable_maskOffer (keep i))
  change (Measure.infinitePi (fun i => (B.individuals i : Measure ℝ))).map (maskIndividualValues keep) =
    Measure.infinitePi (fun i => (maskedProbabilityLaw (B.individuals i) (keep i) : Measure ℝ))
  exact he.trans (congrArg Measure.infinitePi (funext (fun i => (maskedProbabilityLaw_eq_map (B.individuals i) (keep i)).symm)))

end ProphetSecretary.Limiting
