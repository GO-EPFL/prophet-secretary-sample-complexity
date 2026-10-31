import ProphetSecretary.Limiting.CountableCandidates
import ProphetSecretary.Limiting.ConfigurationClockNullSets

/-!
# Arrival regularity on the actual countable probability space

Only present Poisson candidates count as offers. Their analytical band and
array labels serve to construct the probability space; distinct arrival times
make the execution's label tie rule irrelevant almost surely.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance)

lemma individual_clocks_injective :
    ∀ᵐ u ∂individualClocksLaw, Function.Injective u := by
  have hpair (i j : ℕ) : ∀ᵐ u ∂individualClocksLaw, i ≠ j → u i ≠ u j := by
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
    · have h := ProphetSecretary.Probability.indepFun_ae_ne_of_atomless
        (individualClocks_independent.indepFun hij) (measurable_pi_apply i) (measurable_pi_apply j)
        (individualClock_measurePreserving i).hasLaw
        (measurableSet_eq_fun measurable_fst measurable_snd).compl
      exact h.mono fun _ hu _ => hu
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hpair i))] with u hu
  intro i j hij
  by_contra hne
  exact hu i j hne hij

lemma band_clocks_injective :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, ∀ k l j m : ℕ,
      j < (ω k).1 → m < (ω l).1 →
      (configurationPoint j (ω k)).1 = (configurationPoint m (ω l)).1 → k = l ∧ j = m := by
  have hWithin : ∀ᵐ ω ∂B.bandConfigurationsLaw, ∀ k,
      Function.Injective (fun j : Fin (ω k).1 => ((ω k).2 j).1) :=
    ae_all_iff.mpr (fun k => (B.bandConfiguration_measurePreserving k).quasiMeasurePreserving.ae
      (configuration_times_distinct (B.bandIntensity k)))
  have hCross (k l m : ℕ) : ∀ᵐ ω ∂B.bandConfigurationsLaw, k ≠ l →
      ∀ j : Fin (ω k).1, ((ω k).2 j).1 ≠ (configurationPoint m (ω l)).1 := by
    by_cases hkl : k = l
    · exact Filter.Eventually.of_forall (fun _ h => (h hkl).elim)
    · have hI := (B.bandConfigurations_independent.indepFun hkl).comp measurable_id
        (measurable_configurationPoint m).fst
      have h := independent_configuration_times_ne (B.bandIntensity k) hI
        (measurable_pi_apply k) ((measurable_configurationPoint m).fst.comp (measurable_pi_apply l))
        (B.bandConfiguration_measurePreserving k).hasLaw
      exact h.mono fun _ hω _ => hω
  filter_upwards [hWithin,ae_all_iff.mpr (fun k => ae_all_iff.mpr
    (fun l => ae_all_iff.mpr (hCross k l)))] with ω hWithin hCross
  intro k l j m hj hm heq
  by_cases hkl : k = l
  · subst l
    have he : ((ω k).2 ⟨j,hj⟩).1 = ((ω k).2 ⟨m,hm⟩).1 := by
      simpa only [configurationPoint,dif_pos hj,dif_pos hm] using heq
    exact ⟨rfl,congrArg Fin.val (hWithin k he)⟩
  · have hne := hCross k l m hkl ⟨j,hj⟩
    have he : ((ω k).2 ⟨j,hj⟩).1 = (configurationPoint m (ω l)).1 := by
      simpa only [configurationPoint,dif_pos hj] using heq
    exact (hne he).elim

lemma configuration_clocks_ne_individual {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂B.completeWorldLaw ν, ∀ k i : ℕ, ∀ j : Fin (v.1 k).1,
      ((v.1 k).2 j).1 ≠ v.2.2.1 i := by
  have hOne (k i : ℕ) : ∀ᵐ v ∂B.completeWorldLaw ν, ∀ j : Fin (v.1 k).1,
      ((v.1 k).2 j).1 ≠ v.2.2.1 i := by
    have hI := (B.configuration_individual_world_independent ν).comp (measurable_pi_apply k)
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
    have hMP : MeasurePreserving (fun v : CompleteWorld Seed => v.1 k)
        (B.completeWorldLaw ν) (configurationLaw (B.bandIntensity k)) :=
      (B.bandConfiguration_measurePreserving k).comp measurePreserving_fst
    exact independent_configuration_times_ne (B.bandIntensity k) hI
      ((measurable_pi_apply k).comp measurable_fst)
      ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))) hMP.hasLaw
  exact ae_all_iff.mpr (fun k => ae_all_iff.mpr (hOne k))

lemma individualClocks_completeWorld_measurePreserving {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun v : CompleteWorld Seed => v.2.2.1)
      (B.completeWorldLaw ν) individualClocksLaw :=
  measurePreserving_fst.comp (measurePreserving_snd.comp measurePreserving_snd)

/-- All present offers have distinct arrival times on one actual full-world
almost-sure event, including zero-valued individual offers. -/
theorem present_candidate_times_injective {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂B.completeWorldLaw ν,
      Set.InjOn (fun c : Candidate => (candidatePoint v c).1) {c | candidatePresent v c} := by
  have hClock := (B.individualClocks_completeWorld_measurePreserving ν).quasiMeasurePreserving.ae
    individual_clocks_injective
  have hBandMP : MeasurePreserving (Prod.fst : CompleteWorld Seed → BandConfigurations)
      (B.completeWorldLaw ν) B.bandConfigurationsLaw := measurePreserving_fst
  filter_upwards [hClock,hBandMP.quasiMeasurePreserving.ae B.band_clocks_injective,
    B.configuration_clocks_ne_individual ν] with v hClock hBand hMixed
  intro c hc d hd heq
  cases c with
  | inl i =>
    cases d with
    | inl j => exact congrArg Sum.inl (hClock heq)
    | inr lm =>
      change lm.2 < (v.1 lm.1).1 at hd
      have hn := hMixed lm.1 i ⟨lm.2,hd⟩
      have he : ((v.1 lm.1).2 ⟨lm.2,hd⟩).1 = v.2.2.1 i := by
        have he' : (configurationPoint lm.2 (v.1 lm.1)).1 = v.2.2.1 i := heq.symm
        simpa only [configurationPoint,dif_pos hd] using he'
      exact (hn he).elim
  | inr kj =>
    cases d with
    | inl i =>
      change kj.2 < (v.1 kj.1).1 at hc
      have hn := hMixed kj.1 i ⟨kj.2,hc⟩
      have he : ((v.1 kj.1).2 ⟨kj.2,hc⟩).1 = v.2.2.1 i := by
        have he' : (configurationPoint kj.2 (v.1 kj.1)).1 = v.2.2.1 i := heq
        simpa only [configurationPoint,dif_pos hc] using he'
      exact (hn he).elim
    | inr lm =>
      have h := hBand kj.1 lm.1 kj.2 lm.2 hc hd heq
      exact congrArg Sum.inr (Prod.ext h.1 h.2)

theorem present_candidate_times_mem_Ioo {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂B.completeWorldLaw ν, ∀ c : Candidate, candidatePresent v c →
      (candidatePoint v c).1 ∈ Ioo (0 : ℝ) 1 := by
  have hClock : ∀ᵐ u ∂individualClocksLaw, ∀ i, u i ∈ Ioo (0 : ℝ) 1 :=
    ae_all_iff.mpr (fun i => (individualClock_measurePreserving i).quasiMeasurePreserving.ae uniformClock_mem_Ioo)
  have hBandMP : MeasurePreserving (Prod.fst : CompleteWorld Seed → BandConfigurations)
      (B.completeWorldLaw ν) B.bandConfigurationsLaw := measurePreserving_fst
  filter_upwards [(B.individualClocks_completeWorld_measurePreserving ν).quasiMeasurePreserving.ae hClock,
    hBandMP.quasiMeasurePreserving.ae B.bandConfigurations_supported] with v hClock hBand
  intro c hc
  cases c with
  | inl i => exact hClock i
  | inr kj =>
    change kj.2 < (v.1 kj.1).1 at hc
    have h := (hBand kj.1 ⟨kj.2,hc⟩).1
    simpa only [candidatePoint,configurationPoint,dif_pos hc] using h

end ProphetSecretary.Limiting.CountableInstance
