import ProphetSecretary.Stability.UniformScoreStability
import ProphetSecretary.Model.CanonicalWeightNormalization
import Mathlib.Topology.Algebra.Monoid

/-!
# Uniform complete-score stability at arbitrary positive scalar weights

The scalar weights are fixed independently of the array index and policy.
Normalization divides the actual regret by w+c and preserves the canonical
policy on every raw history. The same positive-tail profile controls all
finite dimensions, without a bound on their total first moments.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

lemma Instance.scalarRegret_weightNormalized (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (π : RandomizedPolicy n)
    {w c : ℝ} (hw : 0<w) (hc : 0≤c) :
    optimalScalarValue P (w/(w+c)) (c/(w+c))-
      π.scalarObjective P (w/(w+c)) (c/(w+c))=
      (optimalScalarValue P w c-π.scalarObjective P w c)/(w+c) := by
  have hs : 0<w+c := add_pos_of_pos_of_nonneg hw hc
  rw [div_eq_inv_mul w (w+c),div_eq_inv_mul c (w+c),
    optimalScalarValue_smul P hP (inv_nonneg.mpr hs.le) hw.le hc,
    π.scalarObjective_smul P hP]
  rw [div_eq_inv_mul]
  ring

 theorem finite_uniform_score_stability_positive_weights
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H I w c : ℝ}
    (hH : 0≤H) (hI : 0≤I) (hw : 0<w) (hc : 0<c)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (L : ℝ → ℝ) (hL : ∀ d, 0<d → 0≤L d) (hTail : ∀ m d, 0<d → (P m).tailCount d≤L d)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I) :
    ∃ Ω : ℝ → ℝ, (∀ r, 0≤Ω r ∧ Ω r≤H+1) ∧ Monotone Ω ∧ Ω 0=0 ∧
      Tendsto Ω (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) ∧
      Tendsto (fun r => Real.sqrt (2*I*(H+1)*Ω (r/(w+c)))) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) ∧
      ∀ m (π : RandomizedPolicy (sizes m)) (r : ℝ),
        optimalScalarValue (P m) w c-π.scalarObjective (P m) w c≤r →
        let ρ := (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m)) hw.le hc.le
        |π.expectedRewardScore (P m) (score m)-ρ.expectedRewardScore (P m) (score m)|+
          |π.expectedDurationScore (P m) (score m)-ρ.expectedDurationScore (P m) (score m)|≤
            Real.sqrt (2*I*(H+1)*Ω (r/(w+c))) := by
  have hs : 0<w+c := add_pos hw hc
  let lam := w/(w+c)
  let δ := min (w/(w+c)) (c/(w+c))
  have hδ : 0<δ := lt_min (div_pos hw hs) (div_pos hc hs)
  have hSum : w/(w+c)+c/(w+c)=1 := by rw [←add_div,div_self hs.ne']
  have hComplement : 1-lam=c/(w+c) := by dsimp only [lam]; linarith only [hSum]
  have hRange (_m : ℕ) : lam∈Icc δ (1-δ) := by
    refine ⟨min_le_left _ _,?_⟩
    have hOther : δ≤c/(w+c) := min_le_right _ _
    dsimp only [lam]
    linarith only [hOther,hSum]
  obtain ⟨Ω,hΩ,hMono,hZero,hLim,hRoot,hScore⟩ := finite_uniform_score_stability
    sizes P hH hδ hI hCap L hL hTail (fun _ => lam) hRange score hh hb hm hInfo
  have hRescale : Tendsto (fun r : ℝ => r/(w+c)) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    simpa only [div_eq_mul_inv,zero_mul,id_eq] using Filter.TendstoNhdsWithinIoi.mul_const
      (inv_pos.mpr hs) (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)))
  refine ⟨Ω,hΩ,hMono,hZero,hLim,hRoot.comp hRescale,?_⟩
  intro m π r hr
  let hP := (P m).integrable_maximum_of_bounded (hCap m)
  have hRegret : optimalScalarValue (P m) lam (1-lam)-π.scalarObjective (P m) lam (1-lam)≤r/(w+c) := by
    rw [hComplement]
    change optimalScalarValue (P m) (w/(w+c)) (c/(w+c))-
      π.scalarObjective (P m) (w/(w+c)) (c/(w+c))≤r/(w+c)
    rw [(P m).scalarRegret_weightNormalized hP π hw hc.le]
    exact div_le_div_of_nonneg_right hr hs.le
  let ρ := (P m).valuePolicy hP (div_nonneg hw.le hs.le)
    (show 0≤1-lam from by rw [hComplement]; exact div_nonneg hc.le hs.le)
  have hCanon : ρ=(P m).valuePolicy hP hw.le hc.le := by
    have hThreshold : (fun (_ : Unit) A t i => (P m).valueThreshold lam (1-lam) A t i)=
        fun (_ : Unit) A t i => (P m).valueThreshold w c A t i := by
      funext seed A t i
      rw [hComplement]
      exact ((P m).valueThreshold_weightNormalized hP hw hc.le A t i).symm
    unfold ρ Instance.valuePolicy
    congr 1
    exact congrArg thresholdPolicy hThreshold
  have hBound := hScore m π (r/(w+c)) hRegret
  change |π.expectedRewardScore (P m) (score m)-ρ.expectedRewardScore (P m) (score m)|+
    |π.expectedDurationScore (P m) (score m)-ρ.expectedDurationScore (P m) (score m)|≤
    Real.sqrt (2*I*(H+1)*Ω (r/(w+c))) at hBound
  rw [hCanon] at hBound
  exact hBound

end ProphetSecretary.Model
