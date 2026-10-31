import ProphetSecretary.Probability.ScorePayoffComparison
import ProphetSecretary.Probability.IndependentBandCount

/-!
# Zero-atom compensated scores and bounded payoff expectations

This is the distinct finite score of `con:finite-scores`: band mass is
compensated at zero rather than on the full complement. The actual iid law
and zero-atom lower bound give the stated quantitative L² payoff error.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Probability
variable {Aux : Type*} [MeasurableSpace Aux]

theorem zeroAtomBandScore_payoff_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ν : Measure Aux) [IsProbabilityMeasure ν] {B : Set ℝ} (hB : MeasurableSet B)
    (hB0 : (0:ℝ)∉B) (hq : (1/2:ℝ)≤μ.real {0}) (N : ℕ) (hN : 0<N)
    {intensity D : ℝ} (hp : μ.real B=intensity/(N:ℝ))
    (g : (Fin N → ℝ) × Aux → ℝ) (hg : Measurable g) (hD : 0≤D) (hb : ∀ q, |g q|≤D) :
    |(∫ q, completeScore (fun _ : Fin N => bandScore μ B) q.1*g q ∂(Measure.pi (fun _ : Fin N => μ)).prod ν)-
      ∫ q, (countIn B q.1-intensity)*g q ∂(Measure.pi (fun _ : Fin N => μ)).prod ν|≤
      Real.sqrt (D^2*(2*intensity^2/(N:ℝ))) := by
  let s := fun _ : Fin N => bandScore μ B
  have hm (i : Fin N) : Measurable (s i) := measurable_bandScore μ hB
  have hsB (i : Fin N) : ∀ᵐ x ∂μ, |s i x|≤1 := Eventually.of_forall (bandScore_abs_le_one μ hB0 hq)
  have hs : MemLp (completeScore s) 2 (Measure.pi (fun _ : Fin N => μ)) :=
    (memLp_two_iff_integrable_sq (measurable_completeScore hm).aestronglyMeasurable).mpr
      (completeScore_integrable_pow (fun _ : Fin N => μ) s hm hsB 2)
  have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hNp : (N:ℝ)*μ.real B=intensity := by rw [hp]; field_simp
  have hEq : (fun x : Fin N → ℝ => countIn B x-intensity)=
      centeredIndependentBandCount (fun _ : Fin N => μ) B := by
    funext x
    unfold centeredIndependentBandCount
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hNp]
  have ht : MemLp (fun x : Fin N → ℝ => countIn B x-intensity) 2 (Measure.pi (fun _ : Fin N => μ)) := by
    rw [hEq]
    exact (centeredIndependentBandCount_moments (fun _ : Fin N => μ) hB).1
  exact score_payoff_difference_le_L2 (Measure.pi (fun _ : Fin N => μ)) ν (completeScore s)
    (fun x => countIn B x-intensity) hs ht
    (completeBandScore_centeredCount_L2 μ hB hB0 hq N hN hp) g hg hD hb
end ProphetSecretary.Probability
