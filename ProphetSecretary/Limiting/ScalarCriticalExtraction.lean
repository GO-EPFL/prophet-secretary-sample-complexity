import ProphetSecretary.Limiting.CompactExtraction
import ProphetSecretary.Limiting.NoReserve
import ProphetSecretary.Reach.Robust

/-!
# Critical compact limits at convergent scalar weights

The uniform finite weight estimate first replaces the moving weights by
their interior limit. Actual benchmark and optimal-value convergence then
identify a critical limiting instance on the same extracted subsequence.
Its positive benchmark is retained and its terminal reserve is zero.
Paper correspondence: the compactness step in `updual:modulus`.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical NNReal Topology
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model

lemma normalizedGap_fixedWeight_tendsto_zero (H : ℝ≥0) (sizes : ℕ → ℕ)
    (P : ∀ m, Instance (sizes m)) (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(H : ℝ))
    (lam : ℕ → ℝ) {a : ℝ} (hLam : ∀ m, lam m∈Icc (0 : ℝ) 1) (ha : a∈Icc (0 : ℝ) 1)
    (hLimit : Tendsto lam atTop (𝓝 a))
    (hGap : Tendsto (fun m => normalizedScalarGap (P m) (lam m)) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => normalizedScalarGap (P m) a) atTop (𝓝 (0 : ℝ)) := by
  have hError : Tendsto (fun m => (2*((H : ℝ)+1))*|lam m-a|) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,abs_zero,mul_zero] using (hLimit.sub_const a).abs.const_mul (2*((H : ℝ)+1))
  have hUpper := hGap.add hError
  rw [zero_add] at hUpper
  apply squeeze_zero (fun m => normalizedScalarGap_nonnegative (P m)
    ((P m).integrable_maximum_of_bounded (hcap m)) ha) _ hUpper
  intro m
  have h := normalizedScalarGap_weight_lipschitz_of_bounded (P m) H.coe_nonneg (hcap m) (hLam m) ha
  have hSide := (abs_le.mp h).1
  linarith only [hSide]

theorem exists_critical_ordered_limit (H : ℝ≥0) (mu : ℝ) (hmu : 0<mu) (sizes : ℕ → ℕ)
    (P : ∀ m, Instance (sizes m)) (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(H : ℝ))
    (hMean : ∀ m, mu≤(P m).expectedMaximum) (lam : ℕ → ℝ) {a : ℝ}
    (hLam : ∀ m, lam m∈Icc (0 : ℝ) 1) (ha : a∈Ioo (0 : ℝ) 1)
    (hLimit : Tendsto lam atTop (𝓝 a))
    (hGap : Tendsto (fun m => normalizedScalarGap (P m) (lam m)) atTop (𝓝 (0 : ℝ))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (B : CountableInstance) (wgt : ℝ →ᵇ ℝ),
      B.cap=H ∧ OrderedBandConvergence (fun m => sizes (φ m)) (fun m => P (φ m)) wgt B ∧
      mu≤B.expectedMaximum ∧ B.IsCritical a (1-a) ∧ B.terminal=0 ∧
      Tendsto (fun m => (P (φ m)).expectedMaximum) atTop (𝓝 B.expectedMaximum) ∧
      ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ z∈K, 0≤z.1 ∧ 0≤z.2) →
        TendstoUniformlyOn (fun m z => optimalScalarValue (P (φ m)) z.1 z.2)
          (fun z => B.optimalScalarValue z.1 z.2) atTop K := by
  have hFixed := normalizedGap_fixedWeight_tendsto_zero H sizes P hcap lam hLam ⟨ha.1.le,ha.2.le⟩ hLimit hGap
  obtain ⟨φ,hφ,B,wgt,hCap,hBands,hM,hV,hUniform⟩ := exists_cap_bounded_convergent_subsequence H sizes P hcap
  have hMB : mu≤B.expectedMaximum := ge_of_tendsto hM (Eventually.of_forall (fun m => hMean (φ m)))
  have hBenchmark := ((hM.const_mul a).add_const (1-a)).const_mul optimalCompetitiveRatio
  have hScalar := (hV a (1-a) ha.1.le (sub_nonneg.mpr ha.2.le)).sub hBenchmark
  have hGapB : B.scalarGap a (1-a)=0 := by
    have hSubsequence := hFixed.comp hφ.tendsto_atTop
    exact tendsto_nhds_unique hScalar hSubsequence
  have hCritical : B.IsCritical a (1-a) := ⟨hmu.trans_le hMB,hGapB⟩
  exact ⟨φ,hφ,B,wgt,hCap,hBands,hMB,hCritical,
    B.terminal_eq_zero_of_critical ha.1 (sub_nonneg.mpr ha.2.le) hCritical,hM,hUniform⟩

/-- Interior compactness chooses a limiting weight and extracts the instance
on the same subsequence, preserving the original finite instance laws. -/
theorem exists_critical_ordered_subsequence (H : ℝ≥0) (mu δ : ℝ) (hmu : 0<mu) (hδ : 0<δ)
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m))
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(H : ℝ))
    (hMean : ∀ m, mu≤(P m).expectedMaximum) (lam : ℕ → ℝ)
    (hLam : ∀ m, lam m∈Icc δ (1-δ))
    (hGap : Tendsto (fun m => normalizedScalarGap (P m) (lam m)) atTop (𝓝 (0 : ℝ))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ a∈Icc δ (1-δ), ∃ (B : CountableInstance) (wgt : ℝ →ᵇ ℝ),
      B.cap=H ∧ OrderedBandConvergence (fun m => sizes (φ m)) (fun m => P (φ m)) wgt B ∧
      mu≤B.expectedMaximum ∧ B.IsCritical a (1-a) ∧ B.terminal=0 ∧
      Tendsto (fun m => lam (φ m)) atTop (𝓝 a) ∧
      Tendsto (fun m => (P (φ m)).expectedMaximum) atTop (𝓝 B.expectedMaximum) ∧
      ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ z∈K, 0≤z.1 ∧ 0≤z.2) →
        TendstoUniformlyOn (fun m z => optimalScalarValue (P (φ m)) z.1 z.2)
          (fun z => B.optimalScalarValue z.1 z.2) atTop K := by
  obtain ⟨a,ha,ψ,hψ,hLamLimit⟩ := isCompact_Icc.tendsto_subseq hLam
  have hUnit (m : ℕ) : lam (ψ m)∈Icc (0 : ℝ) 1 :=
    ⟨hδ.le.trans (hLam (ψ m)).1,by linarith only [(hLam (ψ m)).2,hδ]⟩
  have hInterior : a∈Ioo (0 : ℝ) 1 := by constructor <;> linarith only [ha.1,ha.2,hδ]
  obtain ⟨φ,hφ,B,wgt,hCap,hBands,hMB,hCritical,hZero,hM,hUniform⟩ :=
    exists_critical_ordered_limit H mu hmu (fun m => sizes (ψ m)) (fun m => P (ψ m))
      (fun m i => hcap (ψ m) i) (fun m => hMean (ψ m)) (lam ∘ ψ) hUnit hInterior
      hLamLimit (hGap.comp hψ.tendsto_atTop)
  refine ⟨ψ ∘ φ,hψ.comp hφ,a,ha,B,wgt,hCap,hBands,hMB,hCritical,hZero,?_,hM,hUniform⟩
  simpa only [Function.comp_def] using hLamLimit.comp hφ.tendsto_atTop

end ProphetSecretary.Limiting
