import ProphetSecretary.Stability.ScoreStability
import ProphetSecretary.Probability.NormalizedScoreResponse
import ProphetSecretary.Model.PolicySeedTransport

/-!
# Expected likelihood-score stability with arbitrary independent policy seeds

The canonical policy has a singleton seed. Erasing a competitor's independent
seed preserves the joint value/clock law and every complete-vector score.
Thus the proved coupled score bound is an actual difference of the two
expected reward and duration scores.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators ENNReal
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

theorem RandomizedPolicy.expectedScore_stability (π : RandomizedPolicy n) (P : Instance n)
    {H w c I W : ℝ} (hH : 0≤H) (hCap : ∀ i, ∀ᵐ x ∂P.law i, x≤H)
    (hw : 0<w) (hc : 0≤c) (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x|≤1) (hm : ∀ i, (∫ x, h i x ∂P.law i)=0)
    (hInfo : information P.law h≤I) (hMean : π.expectedOutcomeError P w c≤W) :
    let ρ := P.valuePolicy (P.integrable_maximum_of_bounded hCap) hw.le hc
    |π.expectedRewardScore P h-ρ.expectedRewardScore P h|+
      |π.expectedDurationScore P h-ρ.expectedDurationScore P h|≤Real.sqrt (2*I*(H+1)*W) := by
  let hP := P.integrable_maximum_of_bounded hCap
  let ρ := P.valuePolicy hP hw.le hc
  let s : π.World → ℝ := fun ω => completeScore h ω.1
  have hSM := measurable_completeScore hh
  have hBaseLp : MemLp (completeScore h) 2 P.valuesLaw :=
    (memLp_two_iff_integrable_sq hSM.aestronglyMeasurable).mpr (completeScore_integrable_pow P.law h hh hb 2)
  have hValues : MeasurePreserving (Prod.fst : π.World → (Fin n → ℝ)) (P.worldLaw π.seedLaw) P.valuesLaw := measurePreserving_fst
  have hSLp : MemLp s 2 (P.worldLaw π.seedLaw) := hBaseLp.comp_measurePreserving hValues
  have hSI : (∫ ω, (s ω)^2 ∂P.worldLaw π.seedLaw)≤I := by
    have he := hValues.hasLaw.integral_comp (hSM.pow_const 2).aestronglyMeasurable
    exact he.trans_le ((completeScore_secondMoment P.law h hh hb hm).trans_le hInfo)
  let e : π.World → ProphetSecretary.Model.World n Unit := fun ω => (ω.1,(ω.2.1,()))
  have hUnit : MeasurePreserving (fun _ : π.Seed => ()) π.seedLaw (Measure.dirac ()) :=
    ⟨measurable_const,by simp⟩
  have he : MeasurePreserving e (P.worldLaw π.seedLaw) (P.worldLaw (Measure.dirac ())) :=
    (MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Instance.clocksLaw n)).prod hUnit)
  have hRπ : Integrable (fun ω : π.World => s ω*π.realizedReward ω) (P.worldLaw π.seedLaw) := by
    simpa only [s,one_mul,zero_mul,add_zero,mul_comm] using
      π.integrable_scalarScore_of_bounded P hH hCap zero_le_one (le_refl 0) h hh hb
  have hTπ : Integrable (fun ω : π.World => s ω*π.realizedDuration ω) (P.worldLaw π.seedLaw) := by
    simpa only [s,one_mul,zero_mul,zero_add,mul_comm] using
      π.integrable_scalarScore_of_bounded P hH hCap (le_refl 0) zero_le_one h hh hb
  have hRρ : Integrable (fun ω : ρ.World => completeScore h ω.1*ρ.realizedReward ω) (P.worldLaw ρ.seedLaw) := by
    simpa only [one_mul,zero_mul,add_zero,mul_comm] using
      ρ.integrable_scalarScore_of_bounded P hH hCap zero_le_one (le_refl 0) h hh hb
  have hTρ : Integrable (fun ω : ρ.World => completeScore h ω.1*ρ.realizedDuration ω) (P.worldLaw ρ.seedLaw) := by
    simpa only [one_mul,zero_mul,zero_add,mul_comm] using
      ρ.integrable_scalarScore_of_bounded P hH hCap (le_refl 0) zero_le_one h hh hb
  have hRM : Measurable (fun ω : ρ.World => completeScore h ω.1*ρ.realizedReward ω) :=
    (hSM.comp measurable_fst).mul ρ.measurable_realizedReward
  have hTM : Measurable (fun ω : ρ.World => completeScore h ω.1*ρ.realizedDuration ω) :=
    (hSM.comp measurable_fst).mul ρ.measurable_realizedDuration
  have hER : (∫ ω : π.World, s ω*(P.canonicalRule w c).reward () Finset.univ ω.1 ω.2.1 ∂P.worldLaw π.seedLaw)=
      ρ.expectedRewardScore P h := he.hasLaw.integral_comp hRM.aestronglyMeasurable
  have hET : (∫ ω : π.World, s ω*(P.canonicalRule w c).stoppingTime () Finset.univ ω.1 ω.2.1 ∂P.worldLaw π.seedLaw)=
      ρ.expectedDurationScore P h := he.hasLaw.integral_comp hTM.aestronglyMeasurable
  have hRC : Integrable (fun ω : π.World => s ω*(P.canonicalRule w c).reward () Finset.univ ω.1 ω.2.1) (P.worldLaw π.seedLaw) :=
    he.integrable_comp_of_integrable hRρ
  have hTC : Integrable (fun ω : π.World => s ω*(P.canonicalRule w c).stoppingTime () Finset.univ ω.1 ω.2.1) (P.worldLaw π.seedLaw) :=
    he.integrable_comp_of_integrable hTρ
  have hRD : π.expectedRewardScore P h-ρ.expectedRewardScore P h=
      ∫ ω, s ω*π.coupledRewardDifference P w c ω ∂P.worldLaw π.seedLaw := by
    rw [← hER]
    change (∫ ω : π.World, s ω*π.realizedReward ω ∂P.worldLaw π.seedLaw)-
      (∫ ω : π.World, s ω*(P.canonicalRule w c).reward () Finset.univ ω.1 ω.2.1 ∂P.worldLaw π.seedLaw)=_
    rw [← integral_sub hRπ hRC]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by unfold RandomizedPolicy.coupledRewardDifference; ring)
  have hTD : π.expectedDurationScore P h-ρ.expectedDurationScore P h=
      ∫ ω, s ω*π.coupledDurationDifference P w c ω ∂P.worldLaw π.seedLaw := by
    rw [← hET]
    change (∫ ω : π.World, s ω*π.realizedDuration ω ∂P.worldLaw π.seedLaw)-
      (∫ ω : π.World, s ω*(P.canonicalRule w c).stoppingTime () Finset.univ ω.1 ω.2.1 ∂P.worldLaw π.seedLaw)=_
    rw [← integral_sub hTπ hTC]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by unfold RandomizedPolicy.coupledDurationDifference; ring)
  change |π.expectedRewardScore P h-ρ.expectedRewardScore P h|+|π.expectedDurationScore P h-ρ.expectedDurationScore P h|≤_
  rw [hRD,hTD]
  exact π.score_stability P hH hCap hw hc s hSLp hSI hMean
end ProphetSecretary.Model
