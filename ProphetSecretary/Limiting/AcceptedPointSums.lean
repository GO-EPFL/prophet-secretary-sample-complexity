import ProphetSecretary.Limiting.AcceptedPointMeasure
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Reindexing actual accepted-point measures

Countable analytical labels may be regrouped into individual and anonymous
occurrences. These measure identities supply no new observations to a policy.
-/

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace ProphetSecretary.Limiting

lemma measureSum_sumElim {ι κ α : Type*} [MeasurableSpace α]
    (f : ι → Measure α) (g : κ → Measure α) :
    Measure.sum (Sum.elim f g) = Measure.sum f + Measure.sum g := by
  ext S hS
  rw [Measure.sum_apply _ hS,Measure.add_apply,Measure.sum_apply _ hS,Measure.sum_apply _ hS]
  exact ENNReal.summable.tsum_sum ENNReal.summable

lemma measureSum_natPrefix {α : Type*} [MeasurableSpace α] (N : ℕ) (f : Fin N → Measure α) :
    Measure.sum (fun j : ℕ => if hj : j < N then f ⟨j,hj⟩ else 0) = ∑ i : Fin N, f i := by
  ext S hS
  rw [Measure.sum_apply _ hS,Measure.finsetSum_apply]
  rw [tsum_eq_sum (s := Finset.range N)]
  · rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [dif_pos i.isLt]
  · intro j hj
    have hn : ¬j < N := by simpa only [Finset.mem_range] using hj
    rw [dif_neg hn]
    rfl

lemma restricted_countingMeasure (ω : Configuration) {S : Set Point} (hS : MeasurableSet S) :
    (countingMeasure ω).restrict S = ∑ j : Fin ω.1,
      if ω.2 j ∈ S then Measure.dirac (ω.2 j) else 0 := by
  change (∑ j : Fin ω.1, Measure.dirac (ω.2 j)).restrict S = _
  rw [← Measure.sum_fintype,Measure.restrict_sum _ hS,Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  exact restrict_dirac' hS

end ProphetSecretary.Limiting
