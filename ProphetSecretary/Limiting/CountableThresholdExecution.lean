import ProphetSecretary.Limiting.CountableLocalFiniteness

/-!
# Existence of the countable threshold execution

A positive linear continuation floor makes potentially acceptable occurrences
locally finite before the terminal time. Therefore the actual first acceptance
exists, even though there can be infinitely many arrivals near time one. The
floor is an explicit prerequisite; no canonical optimizer is assumed here.
-/

open MeasureTheory Set
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]

lemma CountableRule.admissible_of_linear_floor (π : CountableRule Seed) {γ : ℝ} (hγ : 0 < γ)
    (hfloor : ∀ (v : CompleteWorld Seed) (i : ℕ), π.codeAccepted v i →
      (B.terminal : ℝ) + γ * (1 - codeTime v i) ≤ codeValue v i) :
    π.Admissible B ν := by
  filter_upwards [B.completeWorld_locallyFinite ν] with v hv
  apply FirstAcceptance.hasFirstIfAccepted_of_locallyFinite π.codeAccepted codeTime v
    (fun i hi => hi.2.1.2)
  intro t ht
  let b : ℝ := (B.terminal : ℝ) + γ * (1-t) / 2
  have hpos : 0 < γ * (1-t) := mul_pos hγ (sub_pos.mpr ht)
  have hb : (B.terminal : ℝ) < b := by dsimp only [b]; linarith only [hpos]
  apply (hv b hb).subset
  intro i hi
  change π.codeAccepted v i ∧ codeTime v i ≤ t at hi
  change codePresent v i ∧ b < codeValue v i
  refine ⟨hi.1.1,?_⟩
  have hf := hfloor v i hi.1
  have hm : γ * (1-t) ≤ γ * (1-codeTime v i) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hi.2 1) hγ.le
  dsimp only [b]
  linarith only [hpos,hf,hm]

end ProphetSecretary.Limiting.CountableInstance
