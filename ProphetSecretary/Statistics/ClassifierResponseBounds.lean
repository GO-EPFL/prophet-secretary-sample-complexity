import ProphetSecretary.Statistics.FinitePriorResponseAssembly
import ProphetSecretary.Statistics.FiniteGridResponseLearner
import ProphetSecretary.Model.NumericalCompetitiveBound

/-!
# Endpoint fallback and discarded-mass bounds

The fallback requests no samples and accepts exactly the cap value. Every
learner's reward-or-reach game is at least minus one on cap-one instances.
Discarding invalid prior mass therefore costs at most that mass.
-/

open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

noncomputable def capOnlyFallback (n d : ℕ) : Learner n d where
  Seed := Unit
  seedLaw := Measure.dirac ()
  request _ _ := none
  measurable_request := measurable_const
  decide _ _ _ _ x _ := if x=1 then true else false
  measurable_decide := measurable_const.ite
    (measurableSet_eq_fun (by fun_prop) measurable_const) measurable_const

lemma capOnlyFallback_decide (n d : ℕ) (y : Reservoir n d) (r : Unit)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (capOnlyFallback n d).policy.decide (y,r) t i x H=if x=1 then true else false := rfl

lemma capOnlyFallback_requests (n d : ℕ) (y : Reservoir n d) (r : Unit) (i : Fin n) :
    requests (trainingTranscript (capOnlyFallback n d).request r y) i=0 := by
  unfold trainingTranscript
  cases n*d <;> rfl

lemma Learner.targetGamePayoff_ge_neg_one {n d : ℕ} (L : Learner n d) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (J : Option (Fin n)) {C : ℝ} (hC : C∈Icc (0 : ℝ) 1) :
    -1≤L.targetGamePayoff P J C := by
  cases J with
  | none =>
    have hR : 0 ≤ L.expectedReward P := (L.randomizedPolicy P).expectedReward_nonnegative P
    have hM := P.expectedMaximum_le_of_bounded zero_le_one hcap
    have hM0 := P.expectedMaximum_nonnegative
    have hCM : C*P.expectedMaximum≤1 :=
      (mul_le_mul_of_nonneg_left hM hC.1).trans (by simpa only [mul_one] using hC.2)
    change -1≤L.expectedReward P-C*P.expectedMaximum
    linarith only [hR,hCM]
  | some i =>
    have hR := L.reachProbability_nonnegative P i
    change -1≤L.reachProbability P i-C
    linarith only [hR,hC.2]

lemma discardedMass_game_bound {ι : Type*} [Fintype ι] (w q g : ι → ℝ) {loss : ℝ}
    (hLoss : 0≤loss) (hq : ∀ i, 0≤q i ∧ q i≤w i)
    (hGame : ∀ i, -1≤g i)
    (hGood : -loss*(∑ i, q i)≤∑ i, q i*g i) :
    -loss*(∑ i, w i)-(∑ i, (w i - q i))≤∑ i, w i*g i := by
  have hMass : (∑ i, q i)≤∑ i, w i := Finset.sum_le_sum (fun i _ => (hq i).2)
  have hBad : -(∑ i, (w i - q i))≤∑ i, (w i-q i)*g i := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (hGame i) (sub_nonneg.mpr (hq i).2)
    linarith only [h]
  calc
    _ ≤ -loss*(∑ i, q i)-(∑ i, (w i - q i)) :=
      sub_le_sub_right (mul_le_mul_of_nonpos_left hMass (neg_nonpos.mpr hLoss)) _
    _ ≤ (∑ i, q i*g i)+(∑ i, (w i - q i)*g i) := add_le_add hGood hBad
    _ = _ := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

end ProphetSecretary.Statistics
