import ProphetSecretary.Limiting.ReplacedPremiumDrift
import ProphetSecretary.Limiting.HybridClockMarginal
import ProphetSecretary.Limiting.FinitePotentialMeasurability

/-!
# Sharp original-offer error in the causal comparison

The original replaced clocks are a fixed subfamily of the actual hybrid clocks.
Their constructed uniform product marginal and the value-uniform premium bound
control the stopped generator even when the policy uses all original zero
identities, retained values, auxiliary randomness, and anonymous observations.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n m k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem HybridRule.replacedPremiumCurrentError_bound (π : HybridRule (n + m + k) Seed) (hπ : π.IsMeasurable)
    (Q S : Model.Instance (n + m + k)) (R : Model.Instance m)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {H w c : ℝ}
    (hH : 0 ≤ H) (hcap : ∀ i, ∀ᵐ x ∂R.law i, x ≤ H) (hw : 0 < w) (hc : 0 ≤ c)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    Integrable (π.replacedPremiumCurrentError Q R w c)
      ((hybridWorldLaw S μ ν).prod Model.Instance.uniformClock) ∧
      |∫ q, π.replacedPremiumCurrentError Q R w c q
        ∂(hybridWorldLaw S μ ν).prod Model.Instance.uniformClock| ≤
          (Real.pi / 2) * w * H * Real.sqrt (∑ i, distributionTail R 0 i ^ 2) := by
  let ρ := (hybridWorldLaw S μ ν).prod Model.Instance.uniformClock
  let T := fun q : HybridWorld (n + m + k) Seed × ℝ => q.2
  let U := fun q : HybridWorld (n + m + k) Seed × ℝ => fun j : Fin m => q.1.2.2.1 ((j.natAdd n).castAdd k)
  let V := fun q : HybridWorld (n + m + k) Seed × ℝ => poissonContinuation Q w c q.1.2.2.1 q.2
  let E : Set (HybridWorld (n + m + k) Seed × ℝ) := {q | q.2 ≤ π.realizedDuration q.1}
  let F := fun q : HybridWorld (n + m + k) Seed × ℝ => premiumHazardError R w (V q) (T q) (U q)
  have hTU : MeasurePreserving (fun q => (T q,U q)) ρ
      (Model.Instance.uniformClock.prod (Model.Instance.clocksLaw m)) :=
    hybridTimeRestrictedClocks_measurePreserving S μ ν
      ((Fin.natAddEmb n : Fin m ↪ Fin (n + m)).trans (Fin.castAddEmb k))
  have hV : Measurable V := measurable_poissonContinuationBy Q hQ hw hc T
    (fun q => q.1.2.2.1) measurable_snd (fun j => by fun_prop)
  have hV0 (q : HybridWorld (n + m + k) Seed × ℝ) : 0 ≤ V q :=
    poissonContinuation_nonnegative Q hQ hw.le hc _ _
  have hE : MeasurableSet E :=
    measurableSet_le measurable_snd ((π.measurable_realizedDuration hπ).comp measurable_fst)
  have hG : Integrable (fun q => w * integratedTailHazard R H (T q,U q)) ρ :=
    hTU.integrable_comp_of_integrable ((integrable_integratedTailHazard R H).const_mul w)
  have hFm : Measurable F := measurable_premiumHazardErrorBy R hcap V T U hV
    (measurable_fst.comp hTU.measurable) (fun j => (measurable_pi_apply j).comp (measurable_snd.comp hTU.measurable))
  have hFI : Integrable F ρ := hG.mono' hFm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]
      exact premiumHazardError_abs_le R hcap hw (hV0 q) (T q) (U q))
  have hb := stopped_premiumHazardError_marginal_bound ρ R hH hcap hw T U hTU V hV hV0 E hE
  have heq : E.indicator F = π.replacedPremiumCurrentError Q R w c := by
    funext q
    rfl
  rw [heq] at hb
  have hi := hFI.indicator hE
  rw [heq] at hi
  exact ⟨hi,hb⟩

end ProphetSecretary.Limiting
