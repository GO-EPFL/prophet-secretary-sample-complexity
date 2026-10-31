import ProphetSecretary.Limiting.LabeledResidualData
import ProphetSecretary.Probability.WeakFiniteUpperRestriction

/-!
# Exact residual consistency after taking the original-sequence limit

Retaining one further label removes its actual upper-band marginal. Weak
continuity at the cutoff passes this identity to the limiting positive
residuals. Their atoms at a level depend only on the cloud and the remaining
individuals, not on already retained variables.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal BigOperators
namespace ProphetSecretary.Limiting

lemma labeledBandResidual_succ {n : ℕ} (P : Model.Instance n) (N : ℕ) {b : ℝ} (hb : 0≤b) :
    labeledBandResidual P N b=(labeledPaddedLaw P N).toFiniteMeasure.restrict (Ioi b)+
      labeledBandResidual P (N+1) b := by
  by_cases hN : N<n
  · let k : Fin n := ⟨N,hN⟩
    have hset : Finset.univ.filter (fun i : Fin n => N≤ i.val)=
        insert k (Finset.univ.filter (fun i : Fin n => N+1≤ i.val)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
      constructor
      · intro hi
        by_cases hie : i.val=N
        · exact Or.inl (Fin.ext hie)
        · exact Or.inr (by omega)
      · rintro (rfl | hi)
        · exact le_rfl
        · omega
    have hnot : k∉Finset.univ.filter (fun i : Fin n => N+1≤ i.val) := by simp [k]
    unfold labeledBandResidual
    rw [hset,Finset.sum_insert hnot,labeledPaddedLaw_of_lt P hN]
  · have hzero (M : ℕ) (hNM : N≤M) : Finset.univ.filter (fun i : Fin n => M≤ i.val)=∅ := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      have hn : ¬M≤ i.val := by have hi:=i.isLt; omega
      simp [hn]
    have hpad : (labeledPaddedLaw P N).toFiniteMeasure.restrict (Ioi b)=0 := by
      apply FiniteMeasure.toMeasure_injective
      change (labeledPaddedLaw P N : Measure ℝ).restrict (Ioi b)=0
      rw [labeledPaddedLaw_of_ge P (not_lt.mp hN)]
      simp only [restrict_dirac' measurableSet_Ioi,mem_Ioi,not_lt.mpr hb,if_false]
    rw [hpad]
    simp only [labeledBandResidual,hzero N le_rfl,hzero (N+1) (by omega),Finset.sum_empty,zero_add]

lemma residual_successor_of_weak_limits {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)}
    {Q : ℕ → ProbabilityMeasure ℝ} {ρ : ℕ → FiniteMeasure ℝ} {b : ℝ} (hb : 0≤b)
    (hQ : ∀ i, Tendsto (fun m => labeledPaddedLaw (P m) i) atTop (𝓝 (Q i)))
    (hρ : ∀ N, Tendsto (fun m => labeledBandResidual (P m) N b) atTop (𝓝 (ρ N)))
    (hAtom : ∀ i, (Q i : Measure ℝ) {b}=0) :
    ∀ N, ρ N=(Q N).toFiniteMeasure.restrict (Ioi b)+ρ (N+1) := by
  intro N
  have hQi := ((ProbabilityMeasure.toFiniteMeasure_isEmbedding ℝ).continuous.tendsto (Q N)).comp (hQ N)
  have hCut := ProphetSecretary.Probability.finite_upperRestriction_tendsto hQi b (hAtom N)
  have hSum := hCut.add (hρ (N+1))
  have hEq : (fun m => (labeledPaddedLaw (P m) N).toFiniteMeasure.restrict (Ioi b)+
      labeledBandResidual (P m) (N+1) b)=fun m => labeledBandResidual (P m) N b :=
    funext (fun m => (labeledBandResidual_succ (P m) N hb).symm)
  change Tendsto (fun m => (labeledPaddedLaw (P m) N).toFiniteMeasure.restrict (Ioi b)+
    labeledBandResidual (P m) (N+1) b) atTop (𝓝 ((Q N).toFiniteMeasure.restrict (Ioi b)+ρ (N+1))) at hSum
  rw [hEq] at hSum
  exact tendsto_nhds_unique (hρ N) hSum

private lemma finite_singleton_real_tendsto {ρ : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hρ : Tendsto ρ atTop (𝓝 μ)) (x : ℝ) (hAtom : (μ : Measure ℝ) {x}=0) :
    Tendsto (fun m => (ρ m : Measure ℝ).real {x}) atTop (𝓝 (0 : ℝ)) := by
  let f := ({x} : Set ℝ).indicator (fun _ : ℝ => (1 : ℝ))
  have hFront : (μ : Measure ℝ) (frontier ({x} : Set ℝ))=0 :=
    le_antisymm ((measure_mono (frontier_subset_closure : frontier ({x} : Set ℝ)⊆closure ({x} : Set ℝ))).trans_eq
      (by simpa only [closure_singleton] using hAtom)) bot_le
  have hCont : ∀ᵐ y ∂(μ : Measure ℝ), ContinuousAt f y :=
    (measure_eq_zero_iff_ae_notMem.mp hFront).mono (fun _ hy =>
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousOn.continuousAt_indicator hy)
  have hBound (y : ℝ) : |f y|≤1 := by by_cases hy : y=x <;> simp [f,hy]
  have h := ProphetSecretary.Probability.finite_integral_tendsto_of_weak_ae_continuous_bounded hρ
    (measurable_const.indicator (measurableSet_singleton x)) hBound hCont
  have hIntegral (ν : FiniteMeasure ℝ) : (∫ y, f y ∂(ν : Measure ℝ))=(ν : Measure ℝ).real {x} := by
    rw [integral_indicator_const _ (measurableSet_singleton x),smul_eq_mul,mul_one]
  change Tendsto (fun m => ∫ y, f y ∂(ρ m : Measure ℝ)) atTop
    (𝓝 (∫ y, f y ∂(μ : Measure ℝ))) at h
  simp_rw [hIntegral] at h
  simpa only [measureReal_def,hAtom,ENNReal.toReal_zero] using h

lemma residual_atom_zero_of_remaining_atoms_zero {Q : ℕ → ProbabilityMeasure ℝ}
    {ρ : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ} {b x : ℝ}
    (hSucc : ∀ N, ρ N=(Q N).toFiniteMeasure.restrict (Ioi b)+ρ (N+1))
    (hWeak : Tendsto ρ atTop (𝓝 μ)) (hAtom : (μ : Measure ℝ) {x}=0)
    (N : ℕ) (hQ : ∀ i, N≤ i → (Q i : Measure ℝ) {x}=0) :
    (ρ N : Measure ℝ) {x}=0 := by
  have hStep (i : ℕ) (hNi : N≤ i) : (ρ i : Measure ℝ) {x}=(ρ (i+1) : Measure ℝ) {x} := by
    have he := congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ) {x}) (hSucc i)
    rw [FiniteMeasure.toMeasure_add,Measure.add_apply,FiniteMeasure.restrict_measure_eq,
      Measure.restrict_apply (measurableSet_singleton x)] at he
    have hZero : (Q i : Measure ℝ) ({x}∩Ioi b)=0 :=
      le_antisymm ((measure_mono inter_subset_left).trans_eq (hQ i hNi)) bot_le
    simpa only [ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,hZero,zero_add] using he
  have hConstant (k : ℕ) : (ρ (N+k) : Measure ℝ) {x}=(ρ N : Measure ℝ) {x} := by
    induction k with
    | zero => rw [Nat.add_zero]
    | succ k ih =>
      exact (hStep (N+k) (Nat.le_add_right N k)).symm.trans ih
  have hShift : Tendsto (fun k : ℕ => N+k) atTop atTop :=
    (show StrictMono (fun k : ℕ => N+k) from fun _ _ hk => Nat.add_lt_add_left hk N).tendsto_atTop
  have hLimit := (finite_singleton_real_tendsto hWeak x hAtom).comp hShift
  have hRealConstant (k : ℕ) : (ρ (N+k) : Measure ℝ).real {x}=(ρ N : Measure ℝ).real {x} :=
    congrArg ENNReal.toReal (hConstant k)
  change Tendsto (fun k => (ρ (N+k) : Measure ℝ).real {x}) atTop (𝓝 (0 : ℝ)) at hLimit
  simp_rw [hRealConstant] at hLimit
  have hZero : (ρ N : Measure ℝ).real {x}=0 := tendsto_nhds_unique tendsto_const_nhds hLimit
  exact ((ENNReal.toReal_eq_zero_iff _).mp hZero).resolve_right (measure_ne_top _ _)

end ProphetSecretary.Limiting
