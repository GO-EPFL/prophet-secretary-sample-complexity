import ProphetSecretary.Model.ResponseAlgebra
import ProphetSecretary.Model.SmallSelection

/-!
# Positive selected values under canonical thresholds

Positive duration weight rules out selecting zero before the terminal time.
Uniform clocks have no terminal atom, so a canonical selection is almost surely
positive, while zero observations remain in the executed history.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.canonical_selected_value_positive (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (x u : Fin n → ℝ) (i : Fin n) (hu : u i < 1)
    (hs : (P.valuePolicy hP hw.le hc.le).rule.ActualSelects () Finset.univ x u i) : 0 < x i := by
  have hact := ((P.valuePolicy hP hw.le hc.le).rule.mem_accepted () Finset.univ x u i).mp hs.1.1
  have ht : P.valueThreshold w c (unseen (history Finset.univ x u (u i))) (u i) i ≤ x i := by
    simpa only [Policy.action, Instance.valuePolicy, thresholdPolicy, decide_eq_true_eq] using hact.2
  exact (P.valueThreshold_positive hP hw hc hu _ i).trans_le ht

lemma Instance.canonical_selected_value_positive_ae (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∀ᵐ ω : World n Unit ∂P.worldLaw (Measure.dirac ()), ∀ i,
      (P.valuePolicy hP hw.le hc.le).rule.ActualSelects () Finset.univ ω.1 ω.2.1 i → 0 < ω.1 i := by
  have hn : ∀ᵐ ω : World n Unit ∂P.worldLaw (Measure.dirac ()), ∀ i, ω.2.1 i ≠ 1 :=
    ae_all_iff.mpr (fun i => (P.world_clock_measurePreserving (Measure.dirac ()) i).quasiMeasurePreserving.ae
      (Instance.uniformClock.ae_ne 1))
  filter_upwards [P.world_clocks_mem_unitInterval (Measure.dirac ()), hn] with ω hu hne
  intro i hi
  exact P.canonical_selected_value_positive hP hw hc ω.1 ω.2.1 i
    (lt_of_le_of_ne (hu i).2 (hne i)) hi

/-- The positive-value response is the full acceptance indicator in expectation. -/
theorem Instance.canonical_positiveResponse_eq_oneResponse (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    let π := P.valuePolicy hP hw.le hc.le
    π.selectedResponse P (fun _ x => if 0 < x then 1 else 0) =
      π.selectedResponse P (fun _ _ => 1) := by
  let π := P.valuePolicy hP hw.le hc.le
  change (∫ ω : π.World, π.rule.mappedReward _ ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw π.seedLaw) =
    (∫ ω : π.World, π.rule.mappedReward _ ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw π.seedLaw)
  apply integral_congr_ae
  have hp : ∀ᵐ ω : π.World ∂P.worldLaw π.seedLaw, ∀ i,
      π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i → 0 < ω.1 i := by
    have h := P.canonical_selected_value_positive_ae hP hw hc
    change ∀ᵐ ω : World n Unit ∂P.worldLaw (Measure.dirac ()), ∀ i,
      (P.valuePolicy hP hw.le hc.le).rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i → 0 < ω.1 i
    filter_upwards [h] with ω hω
    rcases ω with ⟨x,u,r⟩
    cases r
    exact hω
  filter_upwards [hp] with ω hω
  unfold Policy.mappedReward
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i
  · simp only [if_pos hs, if_pos (hω i hs)]
  · simp only [if_neg hs]

end ProphetSecretary.Model
