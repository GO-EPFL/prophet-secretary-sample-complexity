import ProphetSecretary.Limiting.HybridPolicy
import ProphetSecretary.Limiting.ConfigurationClockNullSets

/-!
# Actual combined arrival regularity in finite-intensity hybrid instances

Retained clocks and all anonymous clocks are distinct and strictly inside the
unit horizon on one actual almost-sure event. Zero intensity and empty retained
sets are included; no sign assumption on the auxiliary mark law is needed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting

lemma combinedClocks_injective {n N : ℕ} {u : Fin n → ℝ} {v : Fin N → Point}
    (hu : Function.Injective u) (hv : Function.Injective (fun j => (v j).1))
    (hcross : ∀ i j, (v j).1 ≠ u i) : Function.Injective (combinedClocks u v) := by
  intro a b hab
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j =>
      have h : u i = u j := by simpa only [combinedClocks,Fin.addCases_left] using hab
      exact congrArg (Fin.castAdd N) (hu h)
    | right j =>
      have h : u i = (v j).1 := by simpa only [combinedClocks,Fin.addCases_left,Fin.addCases_right] using hab
      exact (hcross i j h.symm).elim
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      have h : (v i).1 = u j := by simpa only [combinedClocks,Fin.addCases_left,Fin.addCases_right] using hab
      exact (hcross j i h).elim
    | right j =>
      have h : (v i).1 = (v j).1 := by simpa only [combinedClocks,Fin.addCases_right] using hab
      exact congrArg (Fin.natAdd n) (hv h)

theorem hybrid_combined_clocks_regular {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂hybridWorldLaw P μ ν,
      Function.Injective (combinedClocks v.2.2.1 v.1.2) ∧
        ∀ i, combinedClocks v.2.2.1 v.1.2 i ∈ Ioo (0 : ℝ) 1 := by
  have hClockMP : MeasurePreserving (fun v : HybridWorld n Seed => v.2.2.1)
      (hybridWorldLaw P μ ν) (Model.Instance.clocksLaw n) :=
    measurePreserving_fst.comp (measurePreserving_snd.comp measurePreserving_snd)
  have hConfigMP : MeasurePreserving (Prod.fst : HybridWorld n Seed → Configuration)
      (hybridWorldLaw P μ ν) (configurationLaw μ) := measurePreserving_fst
  have hCross (i : Fin n) : ∀ᵐ v ∂hybridWorldLaw P μ ν, ∀ j : Fin v.1.1,
      (v.1.2 j).1 ≠ v.2.2.1 i := by
    have hBase : IndepFun Prod.fst Prod.snd (hybridWorldLaw P μ ν) :=
      indepFun_prod measurable_id measurable_id
    have hi := hBase.comp measurable_id ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
    exact independent_configuration_times_ne μ hi measurable_fst
      ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))) hConfigMP.hasLaw
  have hClockOpen : ∀ᵐ u ∂Model.Instance.clocksLaw n, ∀ i, u i ∈ Ioo (0 : ℝ) 1 :=
    ae_all_iff.mpr (fun i => (measurePreserving_eval (fun _ : Fin n => Model.Instance.uniformClock) i).quasiMeasurePreserving.ae uniformClock_mem_Ioo)
  filter_upwards [hClockMP.quasiMeasurePreserving.ae (Model.Instance.clocks_pairwise_distinct (n := n)),
    hConfigMP.quasiMeasurePreserving.ae (configuration_times_distinct μ),
    ae_all_iff.mpr hCross,hClockMP.quasiMeasurePreserving.ae hClockOpen,
    hConfigMP.quasiMeasurePreserving.ae (configuration_times_mem_Ioo μ)] with v hu hv hcross huo hvo
  refine ⟨combinedClocks_injective hu hv hcross,?_⟩
  intro i
  induction i using Fin.addCases with
  | left i => simpa only [combinedClocks,Fin.addCases_left] using huo i
  | right j => simpa only [combinedClocks,Fin.addCases_right] using hvo j

end ProphetSecretary.Limiting
