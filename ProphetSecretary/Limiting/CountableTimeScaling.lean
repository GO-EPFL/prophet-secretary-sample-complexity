import ProphetSecretary.Limiting.CountablePolicy
import ProphetSecretary.Reach.ReachHorizonRescaling

/-!
# Scaling countable arrival observations

Positive time scaling preserves the exact strict-past history of every
individual, including zeros, and maps the anonymous past counting measure.
The seed, all values and all candidate presences are unchanged. This gives a
causal correspondence of physical and normalized horizon observations.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

def scalePointTime (h : ℝ) (p : Point) : Point := (h*p.1,p.2)

def scaleConfigurationTime (h : ℝ) (ω : Configuration) : Configuration :=
  configurationMk ω.1 (fun j => scalePointTime h (ω.2 j))

def scaleCompleteTime (h : ℝ) (v : CompleteWorld Seed) : CompleteWorld Seed :=
  ((fun k => scaleConfigurationTime h (v.1 k)),(v.2.1,((fun i => h*v.2.2.1 i),v.2.2.2)))

def scaleIndividualHistory (h : ℝ) (H : IndividualHistory) : IndividualHistory :=
  fun i => Model.scaleObservation h (H i)

lemma measurable_scalePointTime (h : ℝ) : Measurable (scalePointTime h) :=
  (measurable_fst.const_mul h).prodMk measurable_snd

lemma measurable_scaleConfigurationTime (h : ℝ) : Measurable (scaleConfigurationTime h) := by
  apply measurable_of_configuration_branches
  intro N
  exact (measurable_configuration_mk N).comp
    (measurable_pi_lambda _ (fun j => (measurable_scalePointTime h).comp (measurable_pi_apply j)))

lemma candidatePresent_scaleCompleteTime (h : ℝ) (v : CompleteWorld Seed) (c : Candidate) :
    candidatePresent (scaleCompleteTime h v) c ↔ candidatePresent v c := by cases c <;> rfl

lemma candidatePoint_scaleCompleteTime (h : ℝ) (v : CompleteWorld Seed) (c : Candidate)
    (hc : candidatePresent v c) : candidatePoint (scaleCompleteTime h v) c=scalePointTime h (candidatePoint v c) := by
  cases c with
  | inl i => rfl
  | inr kj =>
    change kj.2 < (v.1 kj.1).1 at hc
    simp only [candidatePoint,scaleCompleteTime,configurationPoint,scaleConfigurationTime,configurationMk,dif_pos hc]

lemma scaleIndividualHistory_history {h : ℝ} (hh : 0 < h) (x u : ℕ → ℝ) (t : ℝ) :
    scaleIndividualHistory h (individualHistory x u t)=
      individualHistory x (fun i => h*u i) (h*t) := by
  funext i
  simp only [scaleIndividualHistory,Model.scaleObservation,individualHistory,mul_lt_mul_iff_right₀ hh]
  split_ifs <;> rfl

lemma observedHistory_scaleConfiguration {h : ℝ} (hh : 0 < h) (ω : Configuration) (t : ℝ) :
    observedHistory (scaleConfigurationTime h ω) (h*t)=
      (observedHistory ω t).map (scalePointTime h) := by
  rcases ω with ⟨N,pts⟩
  change (∑ j : Fin N, if h*(pts j).1 < h*t then Measure.dirac (scalePointTime h (pts j)) else 0)=
    (∑ j : Fin N, if (pts j).1 < t then Measure.dirac (pts j) else 0).map (scalePointTime h)
  rw [← Measure.mapₗ_apply_of_measurable (measurable_scalePointTime h),map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_lt_mul_iff_right₀ hh]
  by_cases hj : (pts j).1 < t
  · rw [if_pos hj,if_pos hj,Measure.mapₗ_apply_of_measurable (measurable_scalePointTime h),
      Measure.map_dirac' (measurable_scalePointTime h)]
  · rw [if_neg hj,if_neg hj,map_zero]

lemma anonymousHistory_scaleCompleteTime {h : ℝ} (hh : 0 < h) (v : CompleteWorld Seed) (t : ℝ) :
    anonymousHistory (scaleCompleteTime h v).1 (h*t)=
      (anonymousHistory v.1 t).map (scalePointTime h) := by
  unfold anonymousHistory
  rw [Measure.map_sum (measurable_scalePointTime h).aemeasurable]
  exact congrArg Measure.sum (funext (fun k => observedHistory_scaleConfiguration hh (v.1 k) t))

variable [MeasurableSpace Seed]

lemma measurable_scaleCompleteTime (h : ℝ) : Measurable (scaleCompleteTime (Seed := Seed) h) := by
  have hCloud : Measurable (fun v : CompleteWorld Seed => fun k => scaleConfigurationTime h (v.1 k)) :=
    measurable_pi_lambda _ (fun k => (measurable_scaleConfigurationTime h).comp ((measurable_pi_apply k).comp measurable_fst))
  have hX : Measurable (fun v : CompleteWorld Seed => v.2.1) := measurable_fst.comp measurable_snd
  have hClock (i : ℕ) : Measurable (fun v : CompleteWorld Seed => v.2.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hU : Measurable (fun v : CompleteWorld Seed => fun i => h*v.2.2.1 i) :=
    measurable_pi_lambda _ (fun i => (hClock i).const_mul h)
  exact hCloud.prodMk (hX.prodMk (hU.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))))

lemma measurable_scaleIndividualHistory (h : ℝ) : Measurable (scaleIndividualHistory h) :=
  measurable_pi_lambda _ (fun i => (Model.measurable_scaleObservation h).comp (measurable_pi_apply i))

end ProphetSecretary.Limiting.CountableInstance
