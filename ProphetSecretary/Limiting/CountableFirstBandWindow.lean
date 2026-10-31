import ProphetSecretary.Limiting.CountableBandScaling

/-!
# Finite prefixes of the Poisson construction bands

The first `N+1` disjoint construction bands form exactly the strict tail
above the `N`th mark cutoff. Setting the intensity factor of this window to
zero empties precisely those finite arrays and leaves all later band laws
unchanged. The cutoff decreases to the terminal reserve.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance

lemma markCutoff_antitone (B : CountableInstance) : Antitone B.markCutoff := by
  intro i j hij
  unfold markCutoff
  apply add_le_add le_rfl
  exact one_div_le_one_div_of_le (by positivity)
    (add_le_add (show (i : ℝ) ≤ j by exact_mod_cast hij) le_rfl)

noncomputable def firstBandWindow (B : CountableInstance) (N : ℕ) : Set ℝ :=
  ⋃ k ∈ Finset.range (N+1), B.markBand k

lemma firstBandWindow_eq_tail (B : CountableInstance) (N : ℕ) :
    B.firstBandWindow N=Ioi (B.markCutoff N) := by
  change (⋃ k ∈ Finset.range (N+1), disjointed (fun j => Ioi (B.markCutoff j)) k)=_
  rw [biUnion_range_succ_disjointed]
  have hMono : Monotone (fun j => Ioi (B.markCutoff j)) := fun i j hij => Ioi_subset_Ioi (B.markCutoff_antitone hij)
  exact congrFun hMono.partialSups_eq N

lemma measurableSet_firstBandWindow (B : CountableInstance) (N : ℕ) :
    MeasurableSet (B.firstBandWindow N) := by rw [B.firstBandWindow_eq_tail]; exact measurableSet_Ioi

lemma markBand_subset_firstBandWindow (B : CountableInstance) {N k : ℕ} (hk : k≤N) :
    B.markBand k ⊆ B.firstBandWindow N := by
  intro x hx
  exact mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk),hx⟩⟩

lemma markBand_disjoint_firstBandWindow (B : CountableInstance) {N k : ℕ} (hk : N<k) :
    Disjoint (B.markBand k) (B.firstBandWindow N) := by
  apply Set.disjoint_left.mpr
  intro x hx hWindow
  obtain ⟨j,hWindow⟩ := mem_iUnion.mp hWindow
  obtain ⟨hj,hxj⟩ := mem_iUnion.mp hWindow
  have hkj : k≠j := by have := Finset.mem_range.mp hj; omega
  exact Set.disjoint_left.mp (B.markBands_disjoint hkj) hx hxj

lemma bandIntensity_supported_markBand (B : CountableInstance) (k : ℕ) :
    ∀ᵐ x ∂(B.bandIntensity k : Measure ℝ), x ∈ B.markBand k :=
  ae_restrict_mem (B.measurableSet_markBand k)

theorem scaleBand_firstBandWindow_bandIntensity (B : CountableInstance) (N k : ℕ) :
    (B.scaleBand (B.firstBandWindow N) 0).bandIntensity k=
      if k≤N then 0 else B.bandIntensity k := by
  rw [B.scaleBand_bandIntensity (B.measurableSet_firstBandWindow N)]
  simp only [bandScaledIntensity,zero_smul,add_zero]
  by_cases hk : k≤N
  · rw [if_pos hk]
    apply FiniteMeasure.toMeasure_injective
    change (B.bandIntensity k : Measure ℝ).restrict (B.firstBandWindow N)ᶜ=0
    apply Measure.restrict_eq_zero.mpr
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [B.bandIntensity_supported_markBand k] with x hx hCompl
    exact hCompl (B.markBand_subset_firstBandWindow hk hx)
  · rw [if_neg hk]
    apply FiniteMeasure.toMeasure_injective
    change (B.bandIntensity k : Measure ℝ).restrict (B.firstBandWindow N)ᶜ=(B.bandIntensity k : Measure ℝ)
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [B.bandIntensity_supported_markBand k] with x hx
    exact fun hWindow => Set.disjoint_left.mp (B.markBand_disjoint_firstBandWindow (lt_of_not_ge hk)) hx hWindow

end ProphetSecretary.Limiting.CountableInstance
