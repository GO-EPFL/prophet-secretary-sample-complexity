import ProphetSecretary.Limiting.HybridPositiveBandSupport

/-!
# Hybrid acceptance gaps along a candidate clock

The gap is weighted acceptance minus actual remaining continuation value.
A retained candidate is removed from its child state; an anonymous candidate
leaves the retained state unchanged. Replacing the retained candidate's own
clock does not change this child-state curve. All original zero identities
still enter the strict-past history.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def FiniteIntensityHybridInstance.candidateGap (B : FiniteIntensityHybridInstance n)
    (w c : ℝ) (candidate : Option (Fin n)) (x : ℝ) (u : Fin n → ℝ) (t : ℝ) : ℝ :=
  w*x-(B.restrictIndividuals (retainedClockState u t candidate)).continuationValue w c (remainingTime t)

lemma measurable_retainedClockState (candidate : Option (Fin n)) :
    Measurable (fun z : (Fin n → ℝ) × ℝ => retainedClockState z.1 z.2 candidate) := by
  have hU (i : Fin n) : Measurable (fun z : (Fin n → ℝ) × ℝ => z.1 i) := (measurable_pi_apply i).comp measurable_fst
  have hState : Measurable (fun z : (Fin n → ℝ) × ℝ =>
      Model.unseen (Model.history Finset.univ (fun _ => 0) z.1 z.2)) :=
    Model.measurable_unseen.comp (Model.measurable_history Finset.univ (fun _ => measurable_const (a := (0 : ℝ))) hU measurable_snd)
  cases candidate with
  | none => exact hState
  | some i => exact (measurable_of_countable (fun A : Finset (Fin n) => A.erase i)).comp hState

lemma FiniteIntensityHybridInstance.measurable_stateElapsedValue (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Measurable (fun z : Finset (Fin n) × ℝ => (B.restrictIndividuals z.1).continuationValue w c (remainingTime z.2)) := by
  apply measurable_from_prod_countable_right
  intro A
  exact (((B.restrictIndividuals A).continuous_continuationValue hw hc).comp continuous_remainingTime).measurable

lemma FiniteIntensityHybridInstance.measurable_candidateGap_joint (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (candidate : Option (Fin n)) :
    Measurable (fun z : ℝ × ((Fin n → ℝ) × ℝ) => B.candidateGap w c candidate z.1 z.2.1 z.2.2) := by
  have hPair : Measurable (fun z : (Fin n → ℝ) × ℝ =>
      (retainedClockState z.1 z.2 candidate, z.2)) :=
    (measurable_retainedClockState candidate).prodMk measurable_snd
  have hV := (B.measurable_stateElapsedValue hw hc).comp hPair
  have hV' := hV.comp (measurable_snd :
    Measurable (fun z : ℝ × ((Fin n → ℝ) × ℝ) => z.2))
  have hX : Measurable (fun z : ℝ × ((Fin n → ℝ) × ℝ) => w*z.1) :=
    measurable_fst.const_mul w
  exact hX.sub hV'

lemma FiniteIntensityHybridInstance.measurable_candidateGap (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (candidate : Option (Fin n)) (x : ℝ) (u : Fin n → ℝ) :
    Measurable (B.candidateGap w c candidate x u) := by
  have hm : Measurable (fun t : ℝ => (x,(u,t))) := by fun_prop
  exact (B.measurable_candidateGap_joint hw hc candidate).comp hm

lemma retainedClockState_update_candidate (u : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    retainedClockState (Function.update u i t) t (some i) = retainedClockState u t (some i) :=
  unseen_updated_clock_erase u i t

lemma FiniteIntensityHybridInstance.candidateGap_update_clock (B : FiniteIntensityHybridInstance n)
    (w c x : ℝ) (u : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    B.candidateGap w c (some i) x (Function.update u i t) t = B.candidateGap w c (some i) x u t := by
  unfold FiniteIntensityHybridInstance.candidateGap
  rw [retainedClockState_update_candidate]

end ProphetSecretary.Limiting
