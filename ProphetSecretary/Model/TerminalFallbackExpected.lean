import ProphetSecretary.Model.TerminalFallbackPerformance

/-!
# Expected performance of the terminal-window fallback

The independent product law yields the exponential failure term; reach events
are never conditioned upon in this estimate.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def RandomizedPolicy.fallbackAfter (π : RandomizedPolicy n) (s ℓ : ℝ) : RandomizedPolicy n where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := π.rule.fallbackAfter s ℓ
  measurable_rule := π.rule.fallbackAfter_isMeasurable π.measurable_rule s ℓ

lemma RandomizedPolicy.fallbackAfter_duration_comparison (π : RandomizedPolicy n) (P : Instance n)
    {η : ℝ} (hη : 0 ≤ η) (ℓ : ℝ) :
    π.expectedDuration P ≤ (π.fallbackAfter (1-η) ℓ).expectedDuration P + η := by
  let T : π.World → ℝ := fun ω => (π.rule.fallbackAfter (1-η) ℓ).stoppingTime
    ω.2.2 Finset.univ ω.1 ω.2.1
  have hTI : Integrable T (P.worldLaw π.seedLaw) := by
    exact (π.fallbackAfter (1-η) ℓ).integrable_realizedDuration P
  have h := integral_mono (π.integrable_realizedDuration P)
    (hTI.add (integrable_const η)) (fun ω : π.World => by
      have ht := π.rule.stoppingTime_le_fallbackAfter_add (by linarith : 1-η ≤ 1) ℓ
        ω.2.2 Finset.univ ω.1 ω.2.1
      change π.rule.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 ≤
        (π.rule.fallbackAfter (1-η) ℓ).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 + η
      convert ht using 1
      ring)
  change π.expectedDuration P ≤ ∫ ω : π.World, T ω + η ∂P.worldLaw π.seedLaw at h
  rw [integral_add hTI (integrable_const η),integral_const] at h
  have he : (∫ ω : π.World, T ω ∂P.worldLaw π.seedLaw) =
      (π.fallbackAfter (1-η) ℓ).expectedDuration P := rfl
  rw [he] at h
  simpa only [probReal_univ,one_smul] using h

lemma RandomizedPolicy.fallbackAfter_reward_comparison (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {η ℓ b H : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hℓ : 0 ≤ ℓ) (hℓb : ℓ ≤ b) (hbH : b ≤ H)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (hπ : ∀ r t i x G, π.rule.decide r t i x G = true → b < x) :
    (∫ ω : π.World, π.realizedTerminalReward b ω ∂P.worldLaw π.seedLaw) ≤
      (π.fallbackAfter (1-η) ℓ).expectedReward P + (b-ℓ) + H*η*P.tailCount b +
        H*Real.exp (-η*P.tailCount ℓ) := by
  let R : π.World → ℝ := fun ω => (π.rule.fallbackAfter (1-η) ℓ).reward
    ω.2.2 Finset.univ ω.1 ω.2.1
  let μ := P.worldLaw π.seedLaw
  let EH : Set π.World := {ω | lateExceedance ω.1 ω.2.1 (1-η) b}
  let EF : Set π.World := {ω | ¬lateExceedance ω.1 ω.2.1 (1-η) ℓ}
  let Jh : π.World → ℝ := fun ω => if ω ∈ EH then 1 else 0
  let Jf : π.World → ℝ := fun ω => if ω ∈ EF then 1 else 0
  have hEH : MeasurableSet EH := measurableSet_lateExceedance _ _
  have hEF : MeasurableSet EF := (measurableSet_lateExceedance _ _).compl
  have hJI (E : Set π.World) (hE : MeasurableSet E) :
      Integrable (fun ω => if ω ∈ E then (1 : ℝ) else 0) μ := by
    apply Integrable.of_bound (Measurable.ite hE measurable_const measurable_const).aestronglyMeasurable 1
    filter_upwards [] with ω
    split_ifs <;> norm_num
  have hJh : Integrable Jh μ := by
    convert hJI EH hEH using 1
    funext ω
    dsimp [Jh]
    split_ifs <;> rfl
  have hJf : Integrable Jf μ := by
    convert hJI EF hEF using 1
    funext ω
    dsimp [Jf]
    split_ifs <;> rfl
  have hJhE : (∫ ω, Jh ω ∂μ) = μ.real EH := by
    simpa only [Jh,Set.indicator_apply,Pi.one_apply] using integral_indicator_one (μ := μ) hEH
  have hJfE : (∫ ω, Jf ω ∂μ) = μ.real EF := by
    simpa only [Jf,Set.indicator_apply,Pi.one_apply] using integral_indicator_one (μ := μ) hEF
  have hvals : ∀ᵐ ω : π.World ∂μ, ∀ i, 0 ≤ ω.1 i ∧ ω.1 i ≤ H := by
    have hv : ∀ᵐ x ∂P.valuesLaw, ∀ i, 0 ≤ x i ∧ x i ≤ H := by
      rw [ae_all_iff]
      intro i
      exact (measurePreserving_eval P.law i).quasiMeasurePreserving.ae ((P.nonnegative i).and (hcap i))
    exact (measurePreserving_fst : MeasurePreserving (fun ω : π.World => ω.1) μ P.valuesLaw).quasiMeasurePreserving.ae hv
  have hu : ∀ᵐ ω : π.World ∂μ, Function.Injective ω.2.1 := by
    exact (measurePreserving_fst.comp (measurePreserving_snd :
      MeasurePreserving (fun ω : π.World => ω.2) μ ((Instance.clocksLaw n).prod π.seedLaw))).quasiMeasurePreserving.ae Instance.clocks_pairwise_distinct
  have hRI : Integrable R μ := by
    exact (π.fallbackAfter (1-η) ℓ).integrable_realizedReward P hP
  have hI := ((hRI.add (integrable_const (b-ℓ))).add
    (hJh.const_mul H)).add (hJf.const_mul H)
  have h := integral_mono_ae (π.integrable_realizedTerminalReward P hP b) hI (by
    filter_upwards [hvals,P.world_clocks_mem_unitInterval π.seedLaw,hu] with ω hx hut hdist
    exact π.rule.terminalReward_le_fallbackAfter_add (1-η) ℓ b H hℓ hℓb hbH hπ
      ω.2.2 ω.1 ω.2.1 hx (fun i => (hut i).2) hdist)
  change (∫ ω : π.World, π.realizedTerminalReward b ω ∂μ) ≤
    ∫ ω : π.World, R ω + (b-ℓ) + H*Jh ω + H*Jf ω ∂μ at h
  rw [integral_add (f := fun ω : π.World => R ω + (b-ℓ) + H*Jh ω)
    (g := fun ω : π.World => H*Jf ω) ((hRI.add (integrable_const (b-ℓ))).add (hJh.const_mul H))
    (hJf.const_mul H),integral_add (f := fun ω : π.World => R ω + (b-ℓ))
    (g := fun ω : π.World => H*Jh ω) (hRI.add (integrable_const (b-ℓ))) (hJh.const_mul H),
    integral_add hRI (integrable_const (b-ℓ)),integral_const,integral_const_mul,
    integral_const_mul,hJhE,hJfE] at h
  simp only [probReal_univ,one_smul] at h
  have hh := P.lateExceedance_probability_le π.seedLaw hη0 hη1 b
  have hf := P.noLateExceedance_probability_le_exp π.seedLaw hη0 hη1 ℓ
  have hH : 0 ≤ H := hℓ.trans (hℓb.trans hbH)
  have hh' := mul_le_mul_of_nonneg_left hh hH
  have hf' := mul_le_mul_of_nonneg_left hf hH
  change μ.real EH ≤ _ at hh
  change μ.real EF ≤ _ at hf
  change H*μ.real EH ≤ _ at hh'
  change H*μ.real EF ≤ _ at hf'
  change (∫ ω : π.World, π.realizedTerminalReward b ω ∂μ) ≤
    (∫ ω, R ω ∂μ) + (b-ℓ) + H*η*P.tailCount b + H*Real.exp (-η*P.tailCount ℓ)
  change (∫ ω : π.World, π.realizedTerminalReward b ω ∂μ) ≤
    (∫ ω, R ω ∂μ) + (b-ℓ) + H*μ.real EH + H*μ.real EF at h
  nlinarith only [h,hh',hf']

lemma RandomizedPolicy.fallbackAfter_scalar_comparison (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {η ℓ b H w c : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hℓ : 0 ≤ ℓ) (hℓb : ℓ ≤ b) (hbH : b ≤ H)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (hπ : ∀ r t i x G, π.rule.decide r t i x G = true → b < x)
    (hw : 0 ≤ w) (hc : 0 ≤ c) :
    π.terminalScalarObjective P b w c ≤
      (π.fallbackAfter (1-η) ℓ).scalarObjective P w c +
        w*(b-ℓ+H*η*P.tailCount b+H*Real.exp (-η*P.tailCount ℓ))+c*η := by
  have hR := mul_le_mul_of_nonneg_left
    (π.fallbackAfter_reward_comparison P hP hη0 hη1 hℓ hℓb hbH hcap hπ) hw
  have hT := mul_le_mul_of_nonneg_left (π.fallbackAfter_duration_comparison P hη0 ℓ) hc
  have hJ : π.terminalScalarObjective P b w c =
      w*(∫ ω : π.World, π.realizedTerminalReward b ω ∂P.worldLaw π.seedLaw)+c*π.expectedDuration P := by
    rw [RandomizedPolicy.terminalScalarObjective,
      integral_add ((π.integrable_realizedTerminalReward P hP b).const_mul w)
        ((π.integrable_realizedDuration P).const_mul c),integral_const_mul,integral_const_mul]
    rfl
  rw [hJ,(π.fallbackAfter (1-η) ℓ).scalarObjective_eq P hP w c]
  nlinarith only [hR,hT]

end ProphetSecretary.Model
