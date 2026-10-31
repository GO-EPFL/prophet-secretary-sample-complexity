import ProphetSecretary.Statistics.FinitePriorAuxiliary
import ProphetSecretary.Statistics.FinitePriorPrefixSampling
import ProphetSecretary.Model.Independence
import ProphetSecretary.Model.Outcome

/-!
# The actual online game covariance factor

The policy receives a training-prefix observation and independent policy seed.
It sees ONLINE values only through the ordinary causal online execution. The
complete online maximum in Gamma is an analytical benchmark, not policy input.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def gameFactor (N : ℕ) (π : Policy (ValueArray n N × Seed) n) (C : ℝ)
    (p : (ValueArray n N × (Fin n → ℝ)) × ((Fin n → ℝ) × Seed)) : ℝ :=
  π.reward (p.1.1,p.2.2) Finset.univ p.1.2 p.2.1-
    π.stoppingTime (p.1.1,p.2.2) Finset.univ p.1.2 p.2.1-
      C*(Instance.maximum p.1.2-1)

lemma measurable_gameFactor (N : ℕ) {π : Policy (ValueArray n N × Seed) n} (hπ : π.IsMeasurable) (C : ℝ) :
    Measurable (gameFactor N π C) := by
  let Ω := (ValueArray n N × (Fin n → ℝ)) × ((Fin n → ℝ) × Seed)
  have hr : Measurable (fun p : Ω => (p.1.1,p.2.2)) := (measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have hx (i : Fin n) : Measurable (fun p : Ω => p.1.2 i) := (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  have hu (i : Fin n) : Measurable (fun p : Ω => p.2.1 i) := (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  exact ((π.measurable_reward hπ hr hx hu Finset.univ).sub
    (π.measurable_stoppingTime hπ hr hx hu Finset.univ)).sub
      (measurable_const.mul ((Instance.measurable_maximum.comp (measurable_snd.comp measurable_fst)).sub measurable_const))

omit [MeasurableSpace Seed] in
lemma gameFactor_abs_le_one (N : ℕ) (π : Policy (ValueArray n N × Seed) n) {C : ℝ}
    (hC : C∈Icc (0:ℝ) 1)
    (p : (ValueArray n N × (Fin n → ℝ)) × ((Fin n → ℝ) × Seed))
    (hx : ∀ i, p.1.2 i∈Icc (0:ℝ) 1) (hu : ∀ i, 0≤p.2.1 i) :
    |gameFactor N π C p|≤1 := by
  have hM0 := Instance.maximum_nonnegative p.1.2
  have hM1 := Instance.maximum_le p.1.2 zero_le_one (fun i => (hx i).2)
  have hR0 := π.reward_nonnegative (p.1.1,p.2.2) Finset.univ p.1.2 p.2.1 (fun i => (hx i).1)
  have hRM := π.reward_le_maximum (p.1.1,p.2.2) Finset.univ p.1.2 p.2.1
  have hT0 := π.stoppingTime_nonneg (p.1.1,p.2.2) Finset.univ p.1.2 p.2.1 hu
  have hT1 := π.stoppingTime_le_one (p.1.1,p.2.2) Finset.univ p.1.2 p.2.1
  unfold gameFactor
  exact abs_le.mpr ⟨by nlinarith [mul_nonneg hC.1 (sub_nonneg.mpr hM1)],by nlinarith [mul_nonneg (sub_nonneg.mpr hC.2) (sub_nonneg.mpr hM1)]⟩

lemma onlineValues_mem_unit_ae (F : FinitePrior n) (N : ℕ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) :
    ∀ᵐ ω ∂F.law N, ∀ i, F.onlineValues ω i∈Icc (0:ℝ) 1 := by
  unfold law
  rw [ae_finsetSum_measure_iff]
  intro θ _
  apply Measure.ae_smul_measure
  have hVals : ∀ᵐ a ∂(F.offerInstance θ).trainingCoordinateLaw (N+1),
      ∀ i, a (i,Fin.last N)∈Icc (0:ℝ) 1 := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun q : Fin n × Fin (N+1) => (F.offerInstance θ).law q.1)
      (i,Fin.last N)).quasiMeasurePreserving.ae (by
        filter_upwards [(F.offerInstance θ).nonnegative i,hcap θ i] with x hx hx1
        exact ⟨hx,hx1⟩)
  exact (measurePreserving_snd (μ:=Measure.dirac θ)).quasiMeasurePreserving.ae hVals

/-- The full source factor has unit absolute bound under the actual finite-prior
experiment, uniform in the causal policy and its arbitrary independent seed. -/
lemma gameFactor_online_bound (F : FinitePrior n) (N b k : ℕ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Policy (ValueArray n N × Seed) n)
    {C : ℝ} (hC : C∈Icc (0:ℝ) 1) :
    ∀ᵐ w ∂F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν),
      |F.onlinePayoff N b k (gameFactor N π C) w|≤1 := by
  have hx := (measurePreserving_fst (μ:=F.law N) (ν:=(Instance.clocksLaw n).prod ν)).quasiMeasurePreserving.ae
    (F.onlineValues_mem_unit_ae N hcap)
  have hu := ((measurePreserving_fst (μ:=Instance.clocksLaw n) (ν:=ν)).comp
    (measurePreserving_snd (μ:=F.law N))).quasiMeasurePreserving.ae (Instance.clocks_mem_unitInterval (n:=n))
  filter_upwards [hx,hu] with w hx hu
  exact gameFactor_abs_le_one N π hC _ hx (fun i => (hu i).1)

/-- The actual policy/game specialization of the covariance term in
`eq:bayes-target-score`. The unused training column is never an online input. -/
theorem gameFactor_covariance_le (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable)
    {C : ℝ} (hC : C∈Icc (0:ℝ) 1) :
    |∫ w, (F.rewardIndicator w.1-F.posterior N b k w.1)*
        F.onlinePayoff N b k (gameFactor N π C) w
      ∂F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν)|≤
      Real.sqrt (∫ ω, (F.posterior N b (k+1) ω-F.posterior N b k ω)^2 ∂F.law N) :=
  F.target_covariance_with_aux_le N b k hk _ (measurable_gameFactor N hπ C)
    (F.gameFactor_online_bound N b k hcap ν π hC)

end ProphetSecretary.Statistics.FinitePrior
