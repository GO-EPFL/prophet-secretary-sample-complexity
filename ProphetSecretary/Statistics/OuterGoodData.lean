import ProphetSecretary.Statistics.OuterLearnerReassembly

/-!
# The two outer confidence events on the actual data space

The retained count uses the cutoff block only. The cap pilot uses its independent
fresh block after that cutoff. Their failure probabilities are each at most 1/m;
their joint good event therefore fails with probability at most 2/m.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n : ℕ}

noncomputable def outerCountGoodData (P : Instance n) (m : ℕ) (hm : 1≤m) : Set (OuterObservedData n m) :=
  {a | (P.retainedAtTag (outerCutoff m hm a.1)).positiveCount≤2*Real.log (m:ℝ)}

noncomputable def outerPilotGoodData (P : Instance n) (m : ℕ) (hm : 1≤m) : Set (OuterObservedData n m) :=
  {a | a.2∈outerPilotGoodAt P m hm (outerCutoff m hm a.1)}

lemma measurableSet_outerCountGoodData (P : Instance n) (m : ℕ) (hm : 1≤m) : MeasurableSet (outerCountGoodData P m hm) :=
  measurableSet_le (P.measurable_retainedAtTag_positiveCount.comp ((measurable_outerCutoff m hm).comp measurable_fst)) measurable_const

lemma measurableSet_outerPilotGoodData (P : Instance n) (m : ℕ) (hm : 1≤m) : MeasurableSet (outerPilotGoodData P m hm) := by
  have hInput : Measurable (fun a : OuterObservedData n m => (outerCutoff m hm a.1,taggedTrainingRows a.2.1 a.2.2)) :=
    ((measurable_outerCutoff m hm).comp measurable_fst).prodMk (measurable_taggedTrainingRows.comp measurable_snd)
  have hSet : outerPilotGoodData P m hm=(fun a : OuterObservedData n m => (outerCutoff m hm a.1,taggedTrainingRows a.2.1 a.2.2)) ⁻¹' outerPilotTaggedGood P m hm := rfl
  rw [hSet]
  exact (measurableSet_outerPilotTaggedGood P m hm).preimage hInput

lemma outerCountGoodData_failure_probability (P : Instance n) (m : ℕ) (hm : 1≤m) :
    (outerObservedDataLaw P m).real (outerCountGoodData P m hm)ᶜ≤1/(m:ℝ) := by
  have hMP : MeasurePreserving (Prod.fst : OuterObservedData n m → Reservoir n m × (Fin m → Fin n → ℝ))
      (outerObservedDataLaw P m) (outerCutoffDataLaw P m) :=
    measurePreserving_fst (μ:=outerCutoffDataLaw P m) (ν:=outerPilotInputsLaw P m)
  let E : Set (Reservoir n m × (Fin m → Fin n → ℝ)) :=
    {p | 2*Real.log (m:ℝ)<(P.retainedAtTag (outerCutoff m hm p)).positiveCount}
  have hE : MeasurableSet E := measurableSet_outerCutoff_positiveCount_failure P m hm
  have hMap := map_measureReal_apply (μ:=outerObservedDataLaw P m) hMP.measurable hE
  rw [hMP.map_eq] at hMap
  have hSet : (outerCountGoodData P m hm)ᶜ=Prod.fst ⁻¹' E := by
    ext a
    simp only [outerCountGoodData,E,Set.mem_compl_iff,Set.mem_setOf_eq,Set.mem_preimage,not_le]
  rw [hSet,←hMap]
  exact outerCutoff_positiveCount_probability P m hm

lemma outerPilotGoodData_failure_probability (P : Instance n) (m : ℕ) (hm : 1≤m) :
    (outerObservedDataLaw P m).real (outerPilotGoodData P m hm)ᶜ≤1/(m:ℝ) := by
  let F : OuterObservedData n m → ℝ := (outerPilotGoodData P m hm).indicator (fun _ => 1)
  have hMeas := measurableSet_outerPilotGoodData P m hm
  have hFm : Measurable F := measurable_const.indicator hMeas
  have hFI : Integrable F (outerObservedDataLaw P m) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable 1
    exact Eventually.of_forall fun a => by
      by_cases ha : a∈outerPilotGoodData P m hm
      · simp only [F,Set.indicator_of_mem ha,norm_one,le_refl]
      · simp only [F,Set.indicator_of_notMem ha,norm_zero,zero_le_one]
  have hInner (p : Reservoir n m × (Fin m → Fin n → ℝ)) :
      (∫ r, F (p,r) ∂outerPilotInputsLaw P m)=(outerPilotInputsLaw P m).real (outerPilotGoodAt P m hm (outerCutoff m hm p)) := by
    have h := integral_indicator_const (μ:=outerPilotInputsLaw P m) (1:ℝ) (measurableSet_outerPilotGoodAt P m hm (outerCutoff m hm p))
    simpa only [F,outerPilotGoodData,Set.indicator_apply,Set.mem_setOf_eq,smul_eq_mul,mul_one] using h
  have hLow (p : Reservoir n m × (Fin m → Fin n → ℝ)) :
      1-1/(m:ℝ)≤∫ r, F (p,r) ∂outerPilotInputsLaw P m := by
    rw [hInner]
    exact outerPilotGoodAt_probability P m hm _
  have hAvg := integral_mono (integrable_const (1-1/(m:ℝ))) hFI.integral_prod_left hLow
  simp only [integral_const,probReal_univ,one_smul] at hAvg
  have hFub := integral_prod F hFI
  have hMass : (∫ a, F a ∂outerObservedDataLaw P m)=(outerObservedDataLaw P m).real (outerPilotGoodData P m hm) := by
    simpa only [smul_eq_mul,mul_one] using integral_indicator_const (μ:=outerObservedDataLaw P m) (1:ℝ) hMeas
  rw [←hFub] at hAvg
  change 1-1/(m:ℝ)≤∫ a, F a ∂outerObservedDataLaw P m at hAvg
  rw [hMass] at hAvg
  rw [probReal_compl_eq_one_sub hMeas]
  linarith only [hAvg]

lemma outerGoodData_failure_probability (P : Instance n) (m : ℕ) (hm : 1≤m) :
    (outerObservedDataLaw P m).real (outerCountGoodData P m hm∩outerPilotGoodData P m hm)ᶜ≤2/(m:ℝ) := by
  rw [Set.compl_inter]
  have hUnion := measureReal_union_le (μ:=outerObservedDataLaw P m) (outerCountGoodData P m hm)ᶜ (outerPilotGoodData P m hm)ᶜ
  have h0 := outerCountGoodData_failure_probability P m hm
  have h1 := outerPilotGoodData_failure_probability P m hm
  have hDouble : (2:ℝ)/(m:ℝ)=1/(m:ℝ)+1/(m:ℝ) := by ring
  rw [hDouble]
  exact hUnion.trans (add_le_add h0 h1)

end ProphetSecretary.Statistics
