import ProphetSecretary.Limiting.FiniteMeasureSubsequence
import Mathlib.MeasureTheory.Measure.SubFinite

/-!
# Order is preserved by weak limits of bounded cap-supported measures

The positive differences have a genuinely weakly convergent subsequence by
Prokhorov compactness. Continuity of addition identifies their limit as the
positive difference of the original two weak limits.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting

lemma weak_cap_mass_closed {H : ℝ} (C : ℝ≥0) {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hMass : ∀ m, (μs m).mass≤C)
    (hCap : ∀ m, (μs m : Measure ℝ) (Icc (0 : ℝ) H)ᶜ=0)
    (hWeak : Tendsto μs atTop (𝓝 μ)) :
    μ.mass≤C ∧ (μ : Measure ℝ) (Icc (0 : ℝ) H)ᶜ=0 := by
  have hClosed := (isCompact_setOf_finiteMeasure_le_of_isCompact (E := ℝ) C (isCompact_Icc : IsCompact (Icc (0 : ℝ) H))).isClosed
  have hMem := hClosed.mem_of_tendsto hWeak
    (Eventually.of_forall (fun m => ⟨hMass m,(FiniteMeasure.null_iff_toMeasure_null (μs m) _).mpr (hCap m)⟩))
  exact ⟨hMem.1,(FiniteMeasure.null_iff_toMeasure_null μ _).mp hMem.2⟩

lemma weak_measure_order_closed {H : ℝ} (hH : 0≤H) (C : ℝ≥0)
    {μs νs : ℕ → FiniteMeasure ℝ} {μ ν : FiniteMeasure ℝ}
    (hMass : ∀ m, (νs m).mass≤C)
    (hCap : ∀ m, (νs m : Measure ℝ) (Icc (0 : ℝ) H)ᶜ=0)
    (hOrder : ∀ m, (μs m : Measure ℝ)≤(νs m : Measure ℝ))
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν)) :
    (μ : Measure ℝ)≤(ν : Measure ℝ) := by
  let δs : ℕ → FiniteMeasure ℝ := fun m =>
    ⟨(νs m : Measure ℝ)-(μs m : Measure ℝ),isFiniteMeasure_of_le (νs m : Measure ℝ) Measure.sub_le⟩
  have hδMass (m : ℕ) : (δs m).mass≤C := by
    apply le_trans _ (hMass m)
    apply ENNReal.coe_le_coe.mp
    simpa only [FiniteMeasure.ennreal_mass,δs,FiniteMeasure.toMeasure_mk] using
      (Measure.le_iff.mp (Measure.sub_le : (δs m : Measure ℝ)≤(νs m : Measure ℝ)) univ MeasurableSet.univ)
  have hδCap (m : ℕ) : (δs m : Measure ℝ) (Icc (0 : ℝ) H)ᶜ=0 :=
    le_antisymm ((Measure.le_iff.mp Measure.sub_le _ measurableSet_Icc.compl).trans_eq (hCap m)) bot_le
  obtain ⟨δ,φ,hφ,_hδMass,_hδCap,hδWeak⟩ :=
    exists_finiteMeasure_weak_subsequence_supported_interval hH C δs hδMass hδCap
  have hExact (m : ℕ) : δs m+μs m=νs m := by
    apply FiniteMeasure.toMeasure_injective
    rw [FiniteMeasure.toMeasure_add]
    exact Measure.sub_add_cancel_of_le (hOrder m)
  have hSum := hδWeak.add (hμ.comp hφ.tendsto_atTop)
  change Tendsto (fun m => δs (φ m)+μs (φ m)) atTop (𝓝 (δ+μ)) at hSum
  simp_rw [hExact] at hSum
  have hEq : ν=δ+μ := tendsto_nhds_unique (hν.comp hφ.tendsto_atTop) hSum
  rw [hEq,FiniteMeasure.toMeasure_add]
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.add_apply]
  exact le_add_of_nonneg_left bot_le

end ProphetSecretary.Limiting
