import ProphetSecretary.Limiting.CountableClockLevelNull
import ProphetSecretary.Limiting.CountableClockNullSets
import ProphetSecretary.Probability.InfiniteErasure

/-!
# Actual retained arrivals do not tie countable continuation values

The excluded-candidate profile is invariant under changing that candidate's
clock. Its erasure is independent of the actual uniform clock by the proved
infinite product-law theorem. Independent actual values are then integrated;
no future clock or offer is supplied to the policy.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting.CountableInstance

lemma unseenMask_history_eq_clockMask (x u : ℕ → ℝ) (t : ℝ) :
    unseenMask (individualHistory x u t) = clockMask u t := by
  funext i
  exact (unseenMask_individualHistory x u t i).trans (unseenMask_individualHistory (fun _ => 0) u t i).symm

lemma clockProfile_at_own_clock_ne_ae (B : CountableInstance) (hZero : B.terminal = 0)
    (i : ℕ) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (x : ℝ) :
    ∀ᵐ clocks ∂individualClocksLaw, B.clockProfile clocks (some i) w c (clocks i) ≠ x := by
  have hI := ProphetSecretary.Probability.infinite_erasure_independent
    (fun _ : ℕ => Model.Instance.uniformClock) i (0 : ℝ)
  have hSwap : Measurable (fun q : ℝ × (ℕ → ℝ) => (q.2,q.1)) := measurable_snd.prodMk measurable_fst
  have hMeas := (B.measurable_clockProfile hw.le hc.le (some i)).comp hSwap
  change Measurable (fun q : ℝ × (ℕ → ℝ) => B.clockProfile q.2 (some i) w c q.1) at hMeas
  have hGraph : MeasurableSet {q : ℝ × (ℕ → ℝ) | B.clockProfile q.2 (some i) w c q.1 ≠ x} :=
    (measurableSet_eq_fun hMeas measurable_const).compl
  have hX : Measurable (fun clocks : ℕ → ℝ => clocks i) := measurable_pi_apply i
  have hY : Measurable (fun clocks : ℕ → ℝ => Function.update clocks i (0 : ℝ)) :=
    ProphetSecretary.Probability.measurable_infinite_erasure i (0 : ℝ)
  have hLaw : HasLaw (fun clocks : ℕ → ℝ => clocks i) Model.Instance.uniformClock individualClocksLaw :=
    (individualClock_measurePreserving i).hasLaw
  have h : ∀ᵐ clocks ∂individualClocksLaw,
      B.clockProfile (Function.update clocks i 0) (some i) w c (clocks i) ≠ x :=
    ProphetSecretary.Probability.indepFun_ae_of_sections (P := individualClocksLaw)
      (μ := Model.Instance.uniformClock) (p := fun t clocks => B.clockProfile clocks (some i) w c t ≠ x)
      hI.symm hX hY hLaw hGraph (fun clocks => B.clockProfile_time_ne_ae hZero clocks (some i) hw hc x)
  filter_upwards [h] with clocks hClocks
  rwa [B.clockProfile_update_candidate clocks i 0 w c (clocks i)] at hClocks

lemma individualValueClock_completeWorld_measurePreserving (B : CountableInstance)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun v : CompleteWorld Seed => (v.2.1,v.2.2.1)) (B.completeWorldLaw ν)
      (B.individualValuesLaw.prod individualClocksLaw) := by
  have hAssoc := (measurePreserving_prodAssoc B.individualValuesLaw individualClocksLaw ν).symm MeasurableEquiv.prodAssoc
  exact (measurePreserving_fst.comp hAssoc).comp measurePreserving_snd

lemma individual_clockProfile_eval_ne_ae (B : CountableInstance) (hZero : B.terminal = 0) (Eval : CountableInstance)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    ∀ᵐ v ∂Eval.completeWorldLaw ν, B.clockProfile v.2.2.1 (some i) w c (v.2.2.1 i) ≠ w*(v.2.1 i) := by
  have hClockPoint : Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) => (q.2,q.2 i)) :=
    measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_snd)
  have hProfile := (B.measurable_clockProfile hw.le hc.le (some i)).comp hClockPoint
  change Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) => B.clockProfile q.2 (some i) w c (q.2 i)) at hProfile
  have hValue : Measurable (fun q : (ℕ → ℝ) × (ℕ → ℝ) => w*(q.1 i)) := by fun_prop
  have hGraph := (measurableSet_eq_fun hProfile hValue).compl
  have hProd : ∀ᵐ q ∂Eval.individualValuesLaw.prod individualClocksLaw,
      B.clockProfile q.2 (some i) w c (q.2 i) ≠ w*(q.1 i) :=
    (Measure.ae_prod_iff_ae_ae hGraph).mpr (Eventually.of_forall fun x =>
      B.clockProfile_at_own_clock_ne_ae hZero i hw hc (w*(x i)))
  exact (Eval.individualValueClock_completeWorld_measurePreserving ν).quasiMeasurePreserving.ae hProd

/-- The equality excluded here is precisely that in the actual individual
callback, with the candidate removed and all observed zero identities present. -/
theorem valueRule_individual_tie_ne_ae (B : CountableInstance) (hZero : B.terminal = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂B.completeWorldLaw ν, ∀ i : ℕ,
      B.continuationValue (eraseMask (unseenMask (individualHistory v.2.1 v.2.2.1 (v.2.2.1 i))) i)
        w c (remainingTime (v.2.2.1 i)) ≠ w*(v.2.1 i) := by
  have h := ae_all_iff.mpr (fun i => B.individual_clockProfile_eval_ne_ae hZero B hw hc ν i)
  filter_upwards [h] with v hv
  intro i
  have hi := hv i
  change B.continuationValue (eraseMask (clockMask v.2.2.1 (v.2.2.1 i)) i) w c
    (remainingTime (v.2.2.1 i)) ≠ w*(v.2.1 i) at hi
  rwa [unseenMask_history_eq_clockMask]

end ProphetSecretary.Limiting.CountableInstance
