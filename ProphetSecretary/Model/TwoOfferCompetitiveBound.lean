import ProphetSecretary.Model.ContinuationODE
import ProphetSecretary.Model.JackpotMoments
import ProphetSecretary.Model.ZeroSimulationProbability
import ProphetSecretary.Reach.RareReach
import Mathlib.Tactic

/-!
# Two-offer benchmarks

The instance-optimal reward is computed from the proved finite Bellman equation.
The resulting rare-jackpot family gives a self-contained upper bound on the global
competitive ratio, with no external numerical theorem as an axiom.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

lemma Instance.optimalReward_oneOffer_mean (P : Instance 1)
    (hP : Integrable maximum P.valuesLaw) : optimalScalarValue P 1 0 = ∫ x, x ∂P.law 0 := by
  rw [P.optimalScalarValue_oneOffer hP zero_le_one le_rfl, zero_add]
  have hp : MeasurePreserving (fun z : ℝ × ℝ => z.1) ((P.law 0).prod uniformClock) (P.law 0) :=
    measurePreserving_fst
  have heq : oneOfferPremium 1 0 =ᵐ[(P.law 0).prod uniformClock] fun z : ℝ × ℝ => z.1 := by
    filter_upwards [hp.quasiMeasurePreserving.ae (P.nonnegative 0)] with z hz
    simp only [oneOfferPremium, one_mul, zero_mul, sub_zero, max_eq_right hz]
  rw [integral_congr_ae heq]
  have h := integral_map (μ := (P.law 0).prod uniformClock) hp.measurable.aemeasurable aestronglyMeasurable_id
  rw [hp.map_eq] at h
  exact h.symm

lemma Instance.optimalReward_singleton_mean {m : ℕ} (P : Instance m) (hm : m = 1)
    (hP : Integrable maximum P.valuesLaw) (i : Fin m) :
    optimalScalarValue P 1 0 = ∫ x, x ∂P.law i := by
  subst m
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi]
  exact P.optimalReward_oneOffer_mean hP

lemma finTwo_eq_rev_of_ne (i j : Fin 2) (h : j ≠ i) : j = i.rev := by
  fin_cases i <;> fin_cases j <;> simp_all

lemma Instance.twoOffer_child_value (P : Instance 2) (hP : Integrable maximum P.valuesLaw)
    (i : Fin 2) : optimalScalarValue (P.restrictTo (remainingSet i)) 1 0 = ∫ x, x ∂P.law i.rev := by
  have hcard : (remainingSet i).card = 1 := by simp [remainingSet]
  let j : Fin (remainingSet i).card := ⟨0, by rw [hcard]; norm_num⟩
  have h := (P.restrictTo (remainingSet i)).optimalReward_singleton_mean hcard
    (P.restrictTo_integrable_maximum _ hP) j
  have he : stateEmbedding (remainingSet i) j = i.rev :=
    finTwo_eq_rev_of_ne i _ (stateEmbedding_remaining_ne i j)
  change optimalScalarValue (P.restrictTo (remainingSet i)) 1 0 = ∫ x, x ∂P.law (stateEmbedding (remainingSet i) j) at h
  rwa [he] at h

lemma Instance.firstChildTimeLaw_two_mass (i : Fin 2) : (firstChildTimeLaw i).real univ = 1 / 2 := by
  calc
    _ = ∫ _t, (1 : ℝ) ∂firstChildTimeLaw i := by simp
    _ = ∫ t in (0 : ℝ)..1, (1 - t) ^ 1 * 1 := integral_firstChildTimeLaw_eq_interval i (fun _ => 1)
    _ = 1 / 2 := by
      simp only [pow_one, mul_one]
      rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun t : ℝ => t)
        intervalIntegrable_const (continuous_id.intervalIntegrable _ _), integral_id]
      norm_num

/-- Exact optimum for two independent offers; timestamps and independent randomization
are already included in the optimized policy class. -/
theorem Instance.optimalReward_twoOffer (P : Instance 2) (hP : Integrable maximum P.valuesLaw) :
    optimalScalarValue P 1 0 =
      ((∫ x, max x (∫ y, y ∂P.law 1) ∂P.law 0) +
        ∫ y, max y (∫ x, x ∂P.law 0) ∂P.law 1) / 2 := by
  rw [P.optimalScalarValue_eq_bellmanValue hP zero_lt_one le_rfl]
  have heach (i : Fin 2) :
      (∫ z, P.bellmanFirstPayoff i 1 0 z ∂(firstChildTimeLaw i).prod (P.law i)) =
        (1 / 2 : ℝ) * ∫ x, max x (∫ y, y ∂P.law i.rev) ∂P.law i := by
    have he : P.bellmanFirstPayoff i 1 0 =
        (fun z : ℝ × ℝ => max z.2 (∫ y, y ∂P.law i.rev)) := by
      funext z
      simp only [bellmanFirstPayoff, zero_mul, zero_add, one_mul,
        bellmanContinuation, P.twoOffer_child_value hP i]
    rw [he]
    have hi : Integrable (fun x : ℝ => max x (∫ y, y ∂P.law i.rev)) (P.law i) :=
      (P.integrable_maximum_iff.mp hP i).sup (integrable_const _)
    rw [integral_prod _ (hi.comp_snd (firstChildTimeLaw i))]
    change (∫ _t : ℝ, (∫ x, max x (∫ y, y ∂P.law i.rev) ∂P.law i) ∂firstChildTimeLaw i) = _
    rw [integral_const]
    simp only [smul_eq_mul, firstChildTimeLaw_two_mass]
  unfold bellmanValue
  simp_rw [heach]
  rw [Fin.sum_univ_two]
  change (1 / 2 : ℝ) * (∫ x, max x (∫ y, y ∂P.law 1) ∂P.law 0) +
    (1 / 2 : ℝ) * (∫ y, max y (∫ x, x ∂P.law 0) ∂P.law 1) = _
  ring

/-- One known offer1 and one rare jackpot, with both identities and timestamps observed. -/
noncomputable def twoOfferJackpot (p : unitInterval) (A : ℝ) (hA : 0 ≤ A) : Instance 2 :=
  (unitOfferInstance.appendZeros 1).jackpot (1 : Fin 2) p A hA

@[simp] lemma twoOfferJackpot_law_zero (p : unitInterval) (A : ℝ) (hA : 0 ≤ A) :
    (twoOfferJackpot p A hA).law 0 = Measure.dirac 1 := by
  simp [twoOfferJackpot, Instance.jackpot, Instance.appendZeros, unitOfferInstance]
  rfl

@[simp] lemma twoOfferJackpot_law_one (p : unitInterval) (A : ℝ) (hA : 0 ≤ A) :
    (twoOfferJackpot p A hA).law 1 = jackpotLaw (Measure.dirac 0) p A := by
  simp [twoOfferJackpot, Instance.jackpot, Instance.appendZeros, unitOfferInstance]
  rfl

lemma twoOfferJackpot_integrable (p : unitInterval) (A : ℝ) (hA : 0 ≤ A) :
    Integrable Instance.maximum (twoOfferJackpot p A hA).valuesLaw :=
  (unitOfferInstance.appendZeros 1).jackpot_integrable_maximum
    (unitOfferInstance.appendZeros_integrable_maximum 1 unitOfferInstance_integrable_maximum) 1 p hA

lemma twoOfferJackpot_mean_zero (p : unitInterval) (A : ℝ) (hA : 0 ≤ A) :
    (∫ x : ℝ, x ∂(twoOfferJackpot p A hA).law 0) = 1 := by simp

lemma twoOfferJackpot_mean_one (p : unitInterval) (A : ℝ) (hA : 0 ≤ A) :
    (∫ x : ℝ, x ∂(twoOfferJackpot p A hA).law 1) = (p : ℝ) * A := by
  rw [twoOfferJackpot_law_one]
  have hf : Integrable (id : ℝ → ℝ) (Measure.dirac 0) := integrable_dirac (by simp)
  simpa only [id_eq, integral_dirac, mul_zero, add_zero] using integral_jackpotLaw hf p A

lemma twoOfferJackpot_max_integral (p : unitInterval) (A : ℝ) (hA : 0 ≤ A)
    (hmean : (p : ℝ) * A = 1) :
    (∫ x, max x 1 ∂(twoOfferJackpot p A hA).law 1) = 2 - (p : ℝ) := by
  have hA1 : 1 ≤ A := by
    have h := mul_le_mul_of_nonneg_right p.2.2 hA
    simpa only [hmean, one_mul] using h
  rw [twoOfferJackpot_law_one]
  have hf : Integrable (fun x : ℝ => max x 1) (Measure.dirac 0) := integrable_dirac (by simp)
  have h := integral_jackpotLaw hf p A
  simp only [max_eq_left hA1, integral_dirac, max_eq_right zero_le_one, hmean, mul_one] at h
  linarith

lemma twoOfferJackpot_expectedMaximum (p : unitInterval) (A : ℝ) (hA : 0 ≤ A)
    (hmean : (p : ℝ) * A = 1) :
    (twoOfferJackpot p A hA).expectedMaximum = 2 - (p : ℝ) := by
  let P := twoOfferJackpot p A hA
  have hX : ∀ᵐ x ∂P.valuesLaw, x (0 : Fin 2) = 1 := by
    have h : ∀ᵐ x ∂P.law (0 : Fin 2), x = (1 : ℝ) := by simp [P]
    exact (measurePreserving_eval P.law 0).quasiMeasurePreserving.ae h
  have hmax : Instance.maximum =ᵐ[P.valuesLaw] fun x => max (x (1 : Fin 2)) 1 := by
    filter_upwards [hX] with x hx
    apply le_antisymm
    · apply Instance.maximum_le x (zero_le_one.trans (le_max_right _ _))
      intro i
      fin_cases i
      · change x (0 : Fin 2) ≤ max (x (1 : Fin 2)) 1
        rw [hx]
        exact le_max_right _ _
      · exact le_max_left _ _
    · exact max_le (Instance.le_maximum x 1) (by simpa only [hx] using Instance.le_maximum x 0)
  unfold Instance.expectedMaximum
  rw [integral_congr_ae hmax]
  have hm := (measurePreserving_eval P.law (1 : Fin 2)).map_eq
  change P.valuesLaw.map (fun x => x 1) = P.law 1 at hm
  have hf : Measurable (fun x : ℝ => max x 1) := measurable_id.max measurable_const
  have h := integral_map (μ := P.valuesLaw) (measurable_pi_apply (1 : Fin 2)).aemeasurable hf.aestronglyMeasurable
  rw [hm] at h
  exact h.symm.trans (twoOfferJackpot_max_integral p A hA hmean)

lemma twoOfferJackpot_optimalReward (p : unitInterval) (A : ℝ) (hA : 0 ≤ A)
    (hmean : (p : ℝ) * A = 1) :
    optimalScalarValue (twoOfferJackpot p A hA) 1 0 = (3 - (p : ℝ)) / 2 := by
  rw [(twoOfferJackpot p A hA).optimalReward_twoOffer (twoOfferJackpot_integrable p A hA),
    twoOfferJackpot_mean_zero, twoOfferJackpot_mean_one, hmean,
    twoOfferJackpot_max_integral p A hA hmean]
  simp
  ring

/-- A self-contained numerical bound sufficient for the coefficient-clamping constants. -/
theorem optimalCompetitiveRatio_le_threeQuarters : optimalCompetitiveRatio ≤ (3 : ℝ) / 4 := by
  apply reach_of_arbitrarily_small_jackpot_error (K := (1 : ℝ) / 4) (by norm_num)
  intro p hp hp1
  let pp : unitInterval := ⟨p, hp.le, hp1⟩
  let A : ℝ := p⁻¹
  have hA : 0 ≤ A := inv_nonneg.mpr hp.le
  have hmean : (pp : ℝ) * A = 1 := mul_inv_cancel₀ hp.ne'
  let P := twoOfferJackpot pp A hA
  have hM : P.expectedMaximum = 2 - p := twoOfferJackpot_expectedMaximum pp A hA hmean
  have hV : optimalScalarValue P 1 0 = (3 - p) / 2 := twoOfferJackpot_optimalReward pp A hA hmean
  have hMp : 0 < P.expectedMaximum := by rw [hM]; linarith
  have hC := optimalCompetitiveRatio_le_instance P ⟨twoOfferJackpot_integrable pp A hA, hMp⟩
  rw [hV] at hC
  have h := (le_div_iff₀ hMp).mp hC
  rw [hM] at h
  have hCp := mul_le_mul_of_nonneg_right optimalCompetitiveRatio_le_one hp.le
  change optimalCompetitiveRatio ≤ 3 / 4 + (1 / 4) * p
  nlinarith

end ProphetSecretary.Model

