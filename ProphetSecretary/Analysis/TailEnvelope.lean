import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Order.IsLUB

/-!
# Bounding a set by its upper-tail envelopes

If the closed upper tail from each point of a bounded-below set has measure
at most K, then the set itself has measure at most K. A minimum is used when
present; otherwise an actual decreasing sequence approaches the infimum and
continuity from below supplies the endpoint argument in `upmom:logtail`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Analysis

theorem measureReal_set_le_of_upperTail (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s : Set ℝ} (hbelow : BddBelow s) {K : ℝ} (hK : 0 ≤ K)
    (htail : ∀ x ∈ s, μ.real (Ici x) ≤ K) : μ.real s ≤ K := by
  by_cases hs : s.Nonempty
  · by_cases hmin : sInf s ∈ s
    · have hsub : s ⊆ Ici (sInf s) := fun x hx => csInf_le hbelow hx
      exact (measureReal_mono hsub).trans (htail _ hmin)
    · obtain ⟨u, hu, hlim, hmem⟩ := exists_seq_tendsto_sInf hs hbelow
      have hmono : Monotone (fun k => Ici (u k)) := by
        intro m n hmn
        exact Ici_subset_Ici.mpr (hu hmn)
      have hsub : s ⊆ ⋃ k, Ici (u k) := by
        intro x hx
        have hlt : sInf s < x := by
          apply lt_of_le_of_ne (csInf_le hbelow hx)
          intro heq
          apply hmin
          rwa [heq]
        have hevent : ∀ᶠ k in atTop, u k < x := (tendsto_order.mp hlim).2 x hlt
        obtain ⟨k, hk⟩ := hevent.exists
        exact mem_iUnion.mpr ⟨k, hk.le⟩
      have hμ (k : ℕ) : μ (Ici (u k)) ≤ ENNReal.ofReal K := by
        calc
          _ = ENNReal.ofReal (μ.real (Ici (u k))) := (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal (htail _ (hmem k))
      have hbound : μ s ≤ ENNReal.ofReal K := by
        apply (measure_mono hsub).trans
        rw [hmono.directed_le.measure_iUnion]
        exact iSup_le hμ
      have hr := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hbound
      simpa only [Measure.real, ENNReal.toReal_ofReal hK] using hr
  · have he : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
    simpa only [he, measureReal_empty] using hK

end ProphetSecretary.Analysis
