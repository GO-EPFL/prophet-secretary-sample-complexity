import ProphetSecretary.Limiting.ThresholdedWorldBandScorePoisson
import ProphetSecretary.Probability.ZeroAtomBandPayoff
import ProphetSecretary.Model.StandbyIidReward

/-!
# Zero-atom finite likelihood scores and actual Poisson score expectations

The iid lower-bound score compensates exclusively at the zero atom. Its
count approximation and the constructed marked Poisson comparison are kept
separate from full-complement compensation.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {Aux : Type*} [MeasurableSpace Aux]

theorem thresholdedWorld_zeroAtomScore_poisson_error (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0≤x) (ν : Measure Aux) [IsProbabilityMeasure ν]
    (N : ℕ) (hN : 0<N) (d : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (hAbove : B⊆Ioi d)
    (hB0 : (0:ℝ)∉B) (hq : (1/2:ℝ)≤κ.real {0}) {a D : ℝ}
    (hp : κ.real B=a/(N:ℝ)) (g : (Measure Point) × Aux → ℝ) (hg : Measurable g)
    (hD : 0≤D) (hb : ∀ q, |g q|≤D) :
    let P := Model.iidOfferInstance κ hκ N
    let μ := ∑ _i : Fin N, thresholdMarkIntensity κ d
    |(∫ ω : Model.World N Aux, completeScore (fun _ : Fin N => bandScore κ B) ω.1*
        g (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2) ∂P.worldLaw ν)-
      ∫ q : Configuration × Aux, ((pointCount (univ ×ˢ B) q.1:ℝ)-a)*g (countingMeasure q.1,q.2)
        ∂(configurationLaw μ).prod ν| ≤ Real.sqrt (D^2*(2*a^2/(N:ℝ)))+
      Real.sqrt (4*D^2*a*((N:ℝ)*(κ.real (Ioi d))^2)) := by
  let P := Model.iidOfferInstance κ hκ N
  let G : Model.World N Aux → ℝ := fun ω =>
    g (thresholdedOfferCountingMeasure d (fun i => (ω.2.1 i,ω.1 i)),ω.2.2)
  have hG : Measurable G := hg.comp (thresholdedPointWorld_measurePreserving P ν d).measurable
  have hZero := zeroAtomBandScore_payoff_error κ ((Model.Instance.clocksLaw N).prod ν) hB hB0 hq N hN
    hp G hG hD (fun ω => hb _)
  have hPoisson := thresholdedWorld_bandScore_poisson_error P ν d hB hAbove g hg hD hb
  have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hNp : (N:ℝ)*κ.real B=a := by rw [hp]; field_simp
  have hSum : (∑ i, (P.law i).real B)=a := by
    simp only [P,Model.iidOfferInstance,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact hNp
  rw [hSum] at hPoisson
  have hCenter (x : Fin N → ℝ) : centeredIndependentBandCount (fun _ : Fin N => κ) B x=countIn B x-a := by
    unfold centeredIndependentBandCount
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hNp]
  simp only [P,Model.iidOfferInstance,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hPoisson
  simp_rw [hCenter] at hPoisson
  apply (abs_sub_le _ (∫ ω : Model.World N Aux, (countIn B ω.1-a)*G ω ∂P.worldLaw ν) _).trans
  exact add_le_add hZero hPoisson
end ProphetSecretary.Limiting
