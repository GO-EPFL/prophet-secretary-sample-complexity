import ProphetSecretary.Statistics.ResponseTrainingSplit
import ProphetSecretary.Statistics.OuterPilotStatistics

/-!
# The independent outer training blocks

A single per-distribution reservoir is split into cutoff, pilot, and inner
blocks. The splitting is a measurable equivalence of the actual product laws.
-/

open MeasureTheory
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

noncomputable def outerReservoirSplit (n h d : ℕ) :
    Reservoir n (h+d) ≃ᵐ (Reservoir n h × Reservoir n d) :=
  (responseTrainingSplit n h d).trans
    ((reservoirCoordinates (n:=n) (k:=h)).symm.prodCongr (MeasurableEquiv.refl (Reservoir n d)))

lemma outerReservoirSplit_measurePreserving {n : ℕ} (P : Instance n) (h d : ℕ) :
    MeasurePreserving (outerReservoirSplit n h d) (P.reservoirLaw (h+d))
      ((P.reservoirLaw h).prod (P.reservoirLaw d)) :=
  ((P.reservoirCoordinates_symm_measurePreserving h).prod (MeasurePreserving.id _)).comp
    (responseTrainingSplit_measurePreserving P h d)

/-- The total number of full sampling rounds. -/
noncomputable def outerSampleBudget (m : ℕ) : ℕ := m+(outerPilotRounds m+4*m)

lemma outerSampleBudget_eq (m : ℕ) : outerSampleBudget m=5*m+500*⌈12*Real.log (2*(m:ℝ))⌉₊ := by
  unfold outerSampleBudget outerPilotRounds outerPilotRank
  omega

noncomputable def outerReservoirBlocks (n m : ℕ) :
    Reservoir n (outerSampleBudget m) ≃ᵐ
      (Reservoir n m × (Reservoir n (outerPilotRounds m) × Reservoir n (4*m))) :=
  (outerReservoirSplit n m (outerPilotRounds m+4*m)).trans
    ((MeasurableEquiv.refl (Reservoir n m)).prodCongr (outerReservoirSplit n (outerPilotRounds m) (4*m)))

lemma outerReservoirBlocks_measurePreserving {n : ℕ} (P : Instance n) (m : ℕ) :
    MeasurePreserving (outerReservoirBlocks n m) (P.reservoirLaw (outerSampleBudget m))
      ((P.reservoirLaw m).prod ((P.reservoirLaw (outerPilotRounds m)).prod (P.reservoirLaw (4*m)))) :=
  by
    have hLeft := outerReservoirSplit_measurePreserving P m (outerPilotRounds m+4*m)
    have hRight := outerReservoirSplit_measurePreserving P (outerPilotRounds m) (4*m)
    exact ((MeasurePreserving.id (P.reservoirLaw m)).prod hRight).comp hLeft

end ProphetSecretary.Statistics
