import ProphetSecretary.Statistics.FinitePriorGameFactor

/-!
# Replacing the hidden target by its current posterior

This is the covariance part of `eq:bayes-target-score`, stated for actual online
executions. It compares the reward-duration surrogate with its posterior-weighted
score. The separate reach-duration comparison and pilot/empirical score lower
bounds are needed to turn this into the full game-payoff bound in the paper.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def gameBaseline (N : ℕ) (π : Policy (ValueArray n N × Seed) n) (C : ℝ)
    (p : (ValueArray n N × (Fin n → ℝ)) × ((Fin n → ℝ) × Seed)) : ℝ :=
  π.stoppingTime (p.1.1,p.2.2) Finset.univ p.1.2 p.2.1-C

lemma measurable_gameBaseline (N : ℕ) {π : Policy (ValueArray n N × Seed) n} (hπ : π.IsMeasurable) (C : ℝ) :
    Measurable (gameBaseline N π C) :=
  (π.measurable_stoppingTime hπ
    ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
    (fun i => (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))
    (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) Finset.univ).sub measurable_const

noncomputable def onlineGameScore (F : FinitePrior n) (N b k : ℕ)
    (π : Policy (ValueArray n N × Seed) n) (C : ℝ)
    (wgt : BaseWorld F N → ℝ) (w : BaseWorld F N × ((Fin n → ℝ) × Seed)) : ℝ :=
  F.onlinePayoff N b k (gameBaseline N π C) w+
    wgt w.1*F.onlinePayoff N b k (gameFactor N π C) w

omit [MeasurableSpace Seed] in
lemma onlineGameScore_eq_mixture (F : FinitePrior n) (N b k : ℕ)
    (π : Policy (ValueArray n N × Seed) n) (C : ℝ)
    (wgt : BaseWorld F N → ℝ) (w : BaseWorld F N × ((Fin n → ℝ) × Seed)) :
    F.onlineGameScore N b k π C wgt w=
      wgt w.1*(π.reward (F.observe N b k w.1,w.2.2) Finset.univ (F.onlineValues w.1) w.2.1-
        C*Instance.maximum (F.onlineValues w.1))+
      (1-wgt w.1)*(π.stoppingTime (F.observe N b k w.1,w.2.2) Finset.univ (F.onlineValues w.1) w.2.1-C) := by
  unfold onlineGameScore onlinePayoff gameBaseline gameFactor
  ring

lemma onlineGameScore_integrable (F : FinitePrior n) (N b k : ℕ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable) {C : ℝ} (hC : C∈Icc (0:ℝ) 1)
    {wgt : BaseWorld F N → ℝ} (hw : Measurable wgt) (hwU : ∀ᵐ ω ∂F.law N, wgt ω∈Icc (0:ℝ) 1) :
    Integrable (F.onlineGameScore N b k π C wgt) (F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν)) := by
  let μ := F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν)
  have hG := F.gameFactor_online_bound N b k hcap ν π hC
  have hGI : Integrable (F.onlinePayoff N b k (gameFactor N π C)) μ :=
    Integrable.of_bound (F.measurable_onlinePayoff N b k (measurable_gameFactor N hπ C)).aestronglyMeasurable 1
      (by simpa only [Real.norm_eq_abs] using hG)
  have hWB : ∀ᵐ ω ∂F.law N, ‖wgt ω‖≤1 := hwU.mono fun ω hω => by
    rw [Real.norm_eq_abs,abs_of_nonneg hω.1]
    exact hω.2
  have hWU : ∀ᵐ w ∂μ, ‖wgt w.1‖≤1 :=
    (measurePreserving_fst (μ:=F.law N) (ν:=(Instance.clocksLaw n).prod ν)).quasiMeasurePreserving.ae hWB
  have hWI : Integrable (fun w => wgt w.1*F.onlinePayoff N b k (gameFactor N π C) w) μ :=
    hGI.bdd_mul (hw.comp measurable_fst).aestronglyMeasurable hWU
  have hBI : Integrable (F.onlinePayoff N b k (gameBaseline N π C)) μ := by
    apply Integrable.of_bound (F.measurable_onlinePayoff N b k (measurable_gameBaseline N hπ C)).aestronglyMeasurable 1
    have hU := ((measurePreserving_fst (μ:=Instance.clocksLaw n) (ν:=ν)).comp
      (measurePreserving_snd (μ:=F.law N))).quasiMeasurePreserving.ae (Instance.clocks_mem_unitInterval (n:=n))
    filter_upwards [hU] with w hU
    change ‖π.stoppingTime (F.observe N b k w.1,w.2.2) Finset.univ (F.onlineValues w.1) w.2.1-C‖≤1
    rw [Real.norm_eq_abs]
    exact unit_abs_sub_le_one
      ⟨π.stoppingTime_nonneg _ _ _ _ (fun i => (hU i).1),π.stoppingTime_le_one _ _ _ _⟩ hC
  exact hBI.add hWI

/-- The hidden-target score loses at most one square-root posterior increment when
replaced by the current training posterior. This does not query online X as training. -/
theorem target_score_ge_posterior_score_sub_increment (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable) {C : ℝ} (hC : C∈Icc (0:ℝ) 1) :
    (∫ w, F.onlineGameScore N b k π C (F.posterior N b k) w
      ∂F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν))-
      Real.sqrt (∫ ω, (F.posterior N b (k+1) ω-F.posterior N b k ω)^2 ∂F.law N)≤
    ∫ w, F.onlineGameScore N b k π C F.rewardIndicator w
      ∂F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν) := by
  have hQ := F.onlineGameScore_integrable N b k hcap ν π hπ hC (F.measurable_rewardIndicator N)
    (Eventually.of_forall F.rewardIndicator_mem_unit)
  have hL := F.onlineGameScore_integrable N b k hcap ν π hπ hC (F.posterior_measurable N b k)
    (F.posterior_mem_unit N b k)
  have hEq : (∫ w, F.onlineGameScore N b k π C F.rewardIndicator w
      ∂F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν))-
      (∫ w, F.onlineGameScore N b k π C (F.posterior N b k) w
      ∂F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν))=
      ∫ w, (F.rewardIndicator w.1-F.posterior N b k w.1)*F.onlinePayoff N b k (gameFactor N π C) w
      ∂F.auxiliaryWorldLaw N ((Instance.clocksLaw n).prod ν) := by
    rw [←integral_sub hQ hL]
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by change _-_= _; unfold onlineGameScore;ring
  have hBound := F.gameFactor_covariance_le N b k hk hcap ν π hπ hC
  rw [←hEq] at hBound
  have h := (abs_le.mp hBound).1
  linarith only [h]

end ProphetSecretary.Statistics.FinitePrior
