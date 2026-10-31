import ProphetSecretary.Model.Bellman
import ProphetSecretary.Model.FirstArrivalChild

/-!
# Integrating the finite first decision

The source experiment separates the observed first prefix from the independent
remaining values and clocks. Every law change below is an explicit measurable
measure-preserving map from the original product model.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

/-- A finite product shuffle used to group observed and future data. -/
lemma measurePreserving_pair_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μa : Measure A) (μb : Measure B) (μc : Measure C) (μd : Measure D)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun z : (A × B) × (C × D) ↦ ((z.1.2, z.2.1), (z.1.1, z.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μb.prod μc).prod (μa.prod μd)) := by
  have h1 := (measurePreserving_prodAssoc (μa.prod μb) μc μd).symm
    MeasurableEquiv.prodAssoc
  have hr := (Measure.measurePreserving_swap (μ := μa) (ν := μb.prod μc)).comp
    (measurePreserving_prodAssoc μa μb μc)
  have h2 := hr.prod (MeasurePreserving.id μd)
  exact (measurePreserving_prodAssoc (μb.prod μc) μa μd).comp (h2.comp h1)

namespace Instance

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

/-- The original world law restricted to a specified first-arrival identity. -/
lemma worldLaw_restrict_firstRegion (P : Instance (n + 1)) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin (n + 1)) :
    (P.worldLaw ν).restrict {ω : World (n + 1) Seed | ω.2.1 ∈ firstRegion i} =
      P.valuesLaw.prod (((clocksLaw (n + 1)).restrict (firstRegion i)).prod ν) := by
  have he : {ω : World (n + 1) Seed | ω.2.1 ∈ firstRegion i} =
      univ ×ˢ ((firstRegion i) ×ˢ univ) := by
    ext ω
    simp only [mem_setOf_eq, mem_prod, mem_univ, and_true, true_and]
  unfold worldLaw
  rw [he, ← Measure.prod_restrict, Measure.restrict_univ,
    ← Measure.prod_restrict, Measure.restrict_univ]

/-- Observed prefix data are original policy seed, first time, and first value. -/
abbrev FirstPrefixData (Seed : Type*) := Seed × (ℝ × ℝ)

abbrev FirstFutureData (i : Fin (n + 1)) :=
  (Fin (remainingSet i).card → ℝ) × (Fin (remainingSet i).card → ℝ)

noncomputable def firstStepLaw (P : Instance (n + 1)) (ν : Measure Seed) (i : Fin (n + 1)) :
    Measure (FirstPrefixData Seed × FirstFutureData i) :=
  (ν.prod ((firstChildTimeLaw i).prod (P.law i))).prod
    ((P.restrictTo (remainingSet i)).valuesLaw.prod (clocksLaw (remainingSet i).card))

noncomputable def firstStepWorld (i : Fin (n + 1))
    (z : FirstPrefixData Seed × FirstFutureData i) : World (n + 1) Seed :=
  (insertCandidate i (z.1.2.2, z.2.1), (firstChildClocks i (z.1.2.1, z.2.2), z.1.1))

/-- The first observation and residual future are independent in this source
experiment. Its pushforward is precisely the original world's first region. -/
theorem firstStepWorld_measurePreserving (P : Instance (n + 1)) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin (n + 1)) :
    MeasurePreserving (firstStepWorld i) (P.firstStepLaw ν i)
      ((P.worldLaw ν).restrict {ω : World (n + 1) Seed | ω.2.1 ∈ firstRegion i}) := by
  haveI : SFinite (firstChildTimeLaw i) := by
    unfold firstChildTimeLaw
    infer_instance
  let Q := P.restrictTo (remainingSet i)
  let T := firstChildTimeLaw i
  let U := clocksLaw (remainingSet i).card
  have h1 := measurePreserving_prodAssoc ν (T.prod (P.law i)) (Q.valuesLaw.prod U)
  have h2 := (MeasurePreserving.id ν).prod (measurePreserving_pair_shuffle T (P.law i) Q.valuesLaw U)
  have h3 := Measure.measurePreserving_swap (μ := ν) (ν := ((P.law i).prod Q.valuesLaw).prod (T.prod U))
  have h4 := measurePreserving_prodAssoc ((P.law i).prod Q.valuesLaw) (T.prod U) ν
  have hvalue := (P.splitCandidate_values_measurePreserving i).symm (splitCandidate i)
  have h5 := hvalue.prod ((firstChildClocks_measurePreserving i).prod (MeasurePreserving.id ν))
  rw [P.worldLaw_restrict_firstRegion ν i]
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-- Add the deterministic singleton seed used for a fixed continuation rule. -/
lemma addUnitSeed_measurePreserving (Q : Instance n) :
    MeasurePreserving (fun z : (Fin n → ℝ) × (Fin n → ℝ) ↦ (z.1, (z.2, ())))
      (Q.valuesLaw.prod (clocksLaw n)) (Q.worldLaw (Measure.dirac ())) := by
  have hu : MeasurePreserving (fun v : Fin n → ℝ ↦ (v, ())) (clocksLaw n)
      ((clocksLaw n).prod (Measure.dirac ())) :=
    ⟨measurable_id.prodMk measurable_const, (Measure.prod_dirac ()).symm⟩
  exact (MeasurePreserving.id Q.valuesLaw).prod hu

/-- First-region partition for arbitrary integrable real world functionals. -/
lemma integral_firstWorldRegion (P : Instance (n + 1)) (ν : Measure Seed)
    [IsProbabilityMeasure ν] {f : World (n + 1) Seed → ℝ}
    (hf : Integrable f (P.worldLaw ν)) :
    (∫ ω, f ω ∂P.worldLaw ν) = ∑ i : Fin (n + 1),
      ∫ ω, f ω ∂(P.worldLaw ν).restrict {ω : World (n + 1) Seed | ω.2.1 ∈ firstRegion i} := by
  let E := fun i : Fin (n + 1) ↦ {ω : World (n + 1) Seed | ω.2.1 ∈ firstRegion i}
  have hE : ∀ i, MeasurableSet (E i) := fun i ↦
    (measurableSet_firstRegion i).preimage (measurable_fst.comp measurable_snd)
  have hpart : ∀ᵐ ω : World (n + 1) Seed ∂P.worldLaw ν,
      (∑ i, (E i).indicator f ω) = f ω := by
    filter_upwards [P.world_clocks_distinct ν] with ω hω
    obtain ⟨i, _hi, hmin⟩ := Finset.exists_min_image Finset.univ ω.2.1 Finset.univ_nonempty
    have hi : ω ∈ E i := fun j ↦ hmin j (Finset.mem_univ j)
    calc
      _ = (E i).indicator f ω := by
        apply Finset.sum_eq_single i
        · intro j _hj hji
          apply Set.indicator_of_notMem
          intro hj
          exact hji (hω (le_antisymm (hj i) (hi j)))
        · intro hn
          exact False.elim (hn (Finset.mem_univ i))
      _ = f ω := Set.indicator_of_mem hi f
  calc
    _ = ∫ ω, ∑ i, (E i).indicator f ω ∂P.worldLaw ν := integral_congr_ae (hpart.mono (fun _ω h ↦ h.symm))
    _ = ∑ i, ∫ ω, (E i).indicator f ω ∂P.worldLaw ν :=
      integral_finsetSum Finset.univ (fun i _hi ↦ hf.indicator (hE i))
    _ = _ := Finset.sum_congr rfl (fun i _hi ↦ integral_indicator (hE i))

lemma integrable_firstStepWorld (P : Instance (n + 1)) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin (n + 1)) {f : World (n + 1) Seed → ℝ}
    (hf : Integrable f (P.worldLaw ν)) :
    Integrable (fun z ↦ f (firstStepWorld i z)) (P.firstStepLaw ν i) :=
  (P.firstStepWorld_measurePreserving ν i).integrable_comp_of_integrable hf.restrict

/-- The first-observation/future experiment reproduces the expected functional
of the full execution, preserving the original policy seed and all value laws. -/
theorem integral_firstStepWorld (P : Instance (n + 1)) (ν : Measure Seed)
    [IsProbabilityMeasure ν] {f : World (n + 1) Seed → ℝ}
    (hfm : Measurable f) (hf : Integrable f (P.worldLaw ν)) :
    (∫ ω, f ω ∂P.worldLaw ν) = ∑ i : Fin (n + 1),
      ∫ z, f (firstStepWorld i z) ∂P.firstStepLaw ν i := by
  rw [P.integral_firstWorldRegion ν hf]
  apply Finset.sum_congr rfl
  intro i _hi
  have hp := P.firstStepWorld_measurePreserving ν i
  have h := integral_map (μ := P.firstStepLaw ν i) hp.measurable.aemeasurable hfm.aestronglyMeasurable
  rw [hp.map_eq] at h
  exact h

/-- Tonelli/Fubini separates the observable first prefix from all future
coordinates. Integrability is inherited from the complete execution law. -/
theorem integral_firstStepWorld_iterated (P : Instance (n + 1)) (ν : Measure Seed)
    [IsProbabilityMeasure ν] {f : World (n + 1) Seed → ℝ}
    (hfm : Measurable f) (hf : Integrable f (P.worldLaw ν)) :
    (∫ ω, f ω ∂P.worldLaw ν) = ∑ i : Fin (n + 1),
      ∫ p : FirstPrefixData Seed,
        (∫ z : FirstFutureData i, f (firstStepWorld i (p, z))
          ∂(P.restrictTo (remainingSet i)).valuesLaw.prod (clocksLaw (remainingSet i).card))
        ∂ν.prod ((firstChildTimeLaw i).prod (P.law i)) := by
  rw [P.integral_firstStepWorld ν hfm hf]
  apply Finset.sum_congr rfl
  intro i _hi
  haveI : SFinite (firstChildTimeLaw i) := by
    unfold firstChildTimeLaw
    infer_instance
  exact integral_prod (fun z ↦ f (firstStepWorld i z)) (P.integrable_firstStepWorld ν i hf)

/-- A raw Unit-seed policy has the same expected payoff after adjoining or
removing its deterministic seed coordinate. -/
lemma integral_unitPolicy_payoff {m : ℕ} (Q : Instance m) (π : Policy Unit m)
    (hπ : π.IsMeasurable) (w c : ℝ) :
    (∫ ω : World m Unit, (w * π.reward ω.2.2 Finset.univ ω.1 ω.2.1 +
      c * π.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1) ∂Q.worldLaw (Measure.dirac ())) =
      ∫ z : (Fin m → ℝ) × (Fin m → ℝ),
        (w * π.reward () Finset.univ z.1 z.2 + c * π.stoppingTime () Finset.univ z.1 z.2)
        ∂Q.valuesLaw.prod (clocksLaw m) := by
  have hm : Measurable (fun ω : World m Unit ↦
      w * π.reward ω.2.2 Finset.univ ω.1 ω.2.1 + c * π.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1) := by
    exact (measurable_const.mul (π.measurable_reward hπ
      (measurable_snd.comp measurable_snd) (fun i ↦ (measurable_pi_apply i).comp measurable_fst)
      (fun i ↦ (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) Finset.univ)).add
      (measurable_const.mul (π.measurable_worldTime hπ Finset.univ))
  have hp := Q.addUnitSeed_measurePreserving
  have h := integral_map (μ := Q.valuesLaw.prod (clocksLaw m)) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at h
  exact h

end Instance
end ProphetSecretary.Model
