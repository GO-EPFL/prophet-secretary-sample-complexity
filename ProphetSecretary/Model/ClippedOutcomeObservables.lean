import ProphetSecretary.Model.ScalarObjectives
import ProphetSecretary.Probability.CenteredValueScore

/-!
# Globally bounded extensions of finite-policy reward and duration

Clipping raw execution payoffs produces measurable observables bounded on the
whole ambient value/clock space. On any actual cap-supported online law they
agree almost everywhere with reward and duration, for every fixed policy.
No Markov or threshold restriction is used for these range facts.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ} {Seed : Type*}

noncomputable def Policy.boundedRewardObservable (π : Policy Seed n) (H : ℝ≥0)
    (r : Seed) (D : Finset (Fin n)) (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  boundedOfferValue H (π.reward r D z.1 z.2)
noncomputable def Policy.boundedDurationObservable (π : Policy Seed n)
    (r : Seed) (D : Finset (Fin n)) (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  boundedOfferValue 1 (π.stoppingTime r D z.1 z.2)

lemma Policy.boundedRewardObservable_bound (π : Policy Seed n) (H : ℝ≥0)
    (r : Seed) (D : Finset (Fin n)) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    |π.boundedRewardObservable H r D z| ≤ H := by
  unfold Policy.boundedRewardObservable
  rw [abs_of_nonneg (boundedOfferValue_mem_range H _).1]
  exact (boundedOfferValue_mem_range H _).2
lemma Policy.boundedDurationObservable_bound (π : Policy Seed n)
    (r : Seed) (D : Finset (Fin n)) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    |π.boundedDurationObservable r D z| ≤ 1 := by
  unfold Policy.boundedDurationObservable
  rw [abs_of_nonneg (boundedOfferValue_mem_range 1 _).1]
  exact (boundedOfferValue_mem_range 1 _).2

lemma Policy.boundedRewardObservable_eq (π : Policy Seed n) (H : ℝ≥0) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) H) :
    π.boundedRewardObservable H r D (x,u) = π.reward r D x u := by
  apply boundedOfferValue_eq H
  exact ⟨π.reward_nonnegative r D x u (fun i => (hx i).1),
    (π.reward_le_maximum r D x u).trans (Instance.maximum_le x H.coe_nonneg (fun i => (hx i).2))⟩
lemma Policy.boundedDurationObservable_eq (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) :
    π.boundedDurationObservable r D (x,u) = π.stoppingTime r D x u :=
  boundedOfferValue_eq 1 ⟨π.stoppingTime_nonneg r D x u hu,π.stoppingTime_le_one r D x u⟩

variable [MeasurableSpace Seed]
lemma Policy.measurable_boundedRewardObservable (π : Policy Seed n) (hπ : π.IsMeasurable)
    (H : ℝ≥0) (r : Seed) (D : Finset (Fin n)) : Measurable (π.boundedRewardObservable H r D) :=
  (boundedOfferValue H).continuous.measurable.comp
    (π.measurable_reward hπ measurable_const (fun i => (measurable_pi_apply i).comp measurable_fst)
      (fun i => (measurable_pi_apply i).comp measurable_snd) D)
lemma Policy.measurable_boundedDurationObservable (π : Policy Seed n) (hπ : π.IsMeasurable)
    (r : Seed) (D : Finset (Fin n)) : Measurable (π.boundedDurationObservable r D) :=
  (boundedOfferValue 1).continuous.measurable.comp
    (π.measurable_stoppingTime hπ measurable_const (fun i => (measurable_pi_apply i).comp measurable_fst)
      (fun i => (measurable_pi_apply i).comp measurable_snd) D)

omit [MeasurableSpace Seed] in
lemma Policy.boundedOutcomeObservables_eq_ae (π : Policy Seed n) (r : Seed) (D : Finset (Fin n))
    (P : Instance n) (H : ℝ≥0) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) :
    ∀ᵐ z : (Fin n → ℝ) × (Fin n → ℝ) ∂P.valuesLaw.prod (Instance.clocksLaw n),
      π.boundedRewardObservable H r D z = π.reward r D z.1 z.2 ∧
      π.boundedDurationObservable r D z = π.stoppingTime r D z.1 z.2 := by
  have hvals : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ∈ Icc (0 : ℝ) H := by
    have hb := ae_all_iff.mpr fun i => (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hcap i)
    filter_upwards [P.ae_nonnegative,hb] with x hx hH
    exact fun i => ⟨hx i,hH i⟩
  have hv := (measurePreserving_fst (μ := P.valuesLaw) (ν := Instance.clocksLaw n)).quasiMeasurePreserving.ae hvals
  have ht := (measurePreserving_snd (μ := P.valuesLaw) (ν := Instance.clocksLaw n)).quasiMeasurePreserving.ae
    (Instance.clocks_mem_unitInterval (n := n))
  filter_upwards [hv,ht] with z hz hu
  exact ⟨π.boundedRewardObservable_eq H r D z.1 z.2 hz,
    π.boundedDurationObservable_eq r D z.1 z.2 (fun i => (hu i).1)⟩

end ProphetSecretary.Model
