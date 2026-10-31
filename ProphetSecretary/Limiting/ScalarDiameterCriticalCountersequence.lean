import ProphetSecretary.Model.ScalarDiameterCountersequence
import ProphetSecretary.Limiting.ScalarCriticalExtraction

/-!
# A critical ordered countersequence for the scalar diameter argument

A failure of the uniform interior estimate gives actual finite instances,
with all class bounds preserved, converging to an interior critical body.
The subsequence remains a countersequence with coefficient m+1. Its labels,
benchmark limit, and compact-uniform scalar-value limits are those of the
same ordered extraction used for score transfer in `updual:modulus`.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical NNReal Topology
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model

theorem exists_critical_scalarDiameter_countersequence (H : ℝ≥0) (S0 mu δ : ℝ)
    (hmu : 0<mu) (hδ : 0<δ)
    (hFail : ∀ K : ℝ, 0≤K → ∃ (n : ℕ) (P : Instance n) (a b : ℝ),
      (∀ i, ∀ᵐ x ∂P.law i, x≤(H : ℝ)) ∧ P.totalFirstMoment≤S0 ∧ mu≤P.expectedMaximum ∧
      a∈Icc δ (1-δ) ∧ b∈Icc δ (1-δ) ∧
      K*(normalizedScalarGap P a+normalizedScalarGap P b)<(b-a)^2) :
    ∃ (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) (a b : ℕ → ℝ) (l : ℝ)
      (B : CountableInstance) (wgt : ℝ →ᵇ ℝ),
      (∀ m i, ∀ᵐ x ∂(P m).law i, x≤(H : ℝ)) ∧
      (∀ m, (P m).totalFirstMoment≤S0) ∧ (∀ m, mu≤(P m).expectedMaximum) ∧
      (∀ m, a m∈Icc δ (1-δ)) ∧ (∀ m, b m∈Icc δ (1-δ)) ∧
      (∀ m : ℕ, ((m : ℝ)+1)*(normalizedScalarGap (P m) (a m)+normalizedScalarGap (P m) (b m))<(b m-a m)^2) ∧
      l∈Icc δ (1-δ) ∧ B.cap=H ∧ B.terminal=0 ∧ mu≤B.expectedMaximum ∧ B.IsCritical l (1-l) ∧
      OrderedBandConvergence sizes P wgt B ∧
      Tendsto (fun m => (a m+b m)/2) atTop (𝓝 l) ∧
      Tendsto (fun m => (P m).expectedMaximum) atTop (𝓝 B.expectedMaximum) ∧
      ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ z∈K, 0≤z.1 ∧ 0≤z.2) →
        TendstoUniformlyOn (fun m z => optimalScalarValue (P m) z.1 z.2)
          (fun z => B.optimalScalarValue z.1 z.2) atTop K := by
  obtain ⟨sizes,P,a,b,hcap,hS,hMean,hA,hB,hStrict,_hGap,hMidGap⟩ :=
    exists_scalarDiameter_countersequence H S0 mu δ hδ hFail
  have hMid (m : ℕ) : (a m+b m)/2∈Icc δ (1-δ) := by
    constructor <;> linarith only [(hA m).1,(hA m).2,(hB m).1,(hB m).2]
  obtain ⟨φ,hφ,l,hl,B,wgt,hCap,hOrdered,hMB,hCritical,hZero,hMidLimit,hM,hUniform⟩ :=
    exists_critical_ordered_subsequence H mu δ hmu hδ sizes P hcap hMean
      (fun m => (a m+b m)/2) hMid hMidGap
  have hStrictSub (m : ℕ) : ((m : ℝ)+1)*
      (normalizedScalarGap (P (φ m)) (a (φ m))+normalizedScalarGap (P (φ m)) (b (φ m)))<
      (b (φ m)-a (φ m))^2 := by
    have hP := (P (φ m)).integrable_maximum_of_bounded (hcap (φ m))
    have hAU : a (φ m)∈Icc (0 : ℝ) 1 :=
      ⟨hδ.le.trans (hA (φ m)).1,by linarith only [(hA (φ m)).2,hδ]⟩
    have hBU : b (φ m)∈Icc (0 : ℝ) 1 :=
      ⟨hδ.le.trans (hB (φ m)).1,by linarith only [(hB (φ m)).2,hδ]⟩
    have hSum : 0≤normalizedScalarGap (P (φ m)) (a (φ m))+normalizedScalarGap (P (φ m)) (b (φ m)) :=
      add_nonneg (normalizedScalarGap_nonnegative _ hP hAU) (normalizedScalarGap_nonnegative _ hP hBU)
    have hIndex : (m : ℝ)+1≤(φ m : ℝ)+1 := by exact_mod_cast Nat.succ_le_succ (hφ.id_le m)
    exact (mul_le_mul_of_nonneg_right hIndex hSum).trans_lt (hStrict (φ m))
  exact ⟨(fun m => sizes (φ m)),(fun m => P (φ m)),(fun m => a (φ m)),(fun m => b (φ m)),
    l,B,wgt,(fun m i => hcap (φ m) i),(fun m => hS (φ m)),(fun m => hMean (φ m)),
    (fun m => hA (φ m)),(fun m => hB (φ m)),hStrictSub,hl,hCap,hZero,hMB,hCritical,
    hOrdered,hMidLimit,hM,hUniform⟩

end ProphetSecretary.Limiting
