import ProphetSecretary.Model.OuterRetentionTailCount
import ProphetSecretary.Probability.OrderedSplitMean

/-!
# The retained mean at every fixed tagged cutoff

The void event is an actual product event of the fresh independent offer/tag
vector. Off that event, at least one retained offer attains the numerical maximum.
The discarded event is a lower numerical fraction, including partial atom ties.
Fixed-cutoff form of `upouter:retainedmean`.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model.Instance
variable {n : ℕ}

def taggedVoidEvent (t : ℝ × ℝ) : Set (Fin n → ℝ × ℝ) := {z | ∀ i, ¬taggedAbove t (z i)}

lemma measurableSet_taggedAbove_fixed (t : ℝ × ℝ) : MeasurableSet {z : ℝ × ℝ | taggedAbove t z} :=
  measurableSet_taggedAbove.preimage (measurable_const.prodMk measurable_id)

lemma measurableSet_taggedVoidEvent (t : ℝ × ℝ) : MeasurableSet (taggedVoidEvent (n:=n) t) := by
  convert MeasurableSet.iInter (fun i : Fin n => (measurableSet_taggedAbove_fixed t).compl.preimage (measurable_pi_apply i)) using 1
  ext z
  simp only [taggedVoidEvent,Set.mem_setOf_eq,Set.mem_iInter,Set.mem_preimage,Set.mem_compl_iff]

lemma taggedVoidEvent_probability (P : Instance n) (t : ℝ × ℝ) :
    P.taggedValuesLaw.real (taggedVoidEvent t)=P.taggedVoidProbability t := by
  have hSet : taggedVoidEvent (n:=n) t=Set.univ.pi (fun _ : Fin n => {z : ℝ × ℝ | ¬taggedAbove t z}) := by
    ext z
    simp only [taggedVoidEvent,Set.mem_setOf_eq,Set.mem_pi,Set.mem_univ,forall_true_left]
  change (P.taggedValuesLaw (taggedVoidEvent t)).toReal=_
  rw [hSet,taggedValuesLaw,Measure.pi_pi,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact probReal_compl_eq_one_sub (μ:=(P.law i).prod uniformClock) (measurableSet_taggedAbove_fixed t)

lemma maximum_retainedAtTag_eq (t : ℝ × ℝ) (z : Fin n → ℝ × ℝ) :
    maximum (fun i => retainAboveTag t (z i))=if z∈taggedVoidEvent t then 0 else maximum (fun i => (z i).1) := by
  by_cases hVoid : z∈taggedVoidEvent t
  · rw [if_pos hVoid]
    apply le_antisymm _ (maximum_nonnegative _)
    apply maximum_le _ le_rfl
    intro i
    exact (if_neg (hVoid i)).le
  · rw [if_neg hVoid]
    obtain ⟨j,hj⟩ : ∃ j, taggedAbove t (z j) := by
      simpa only [taggedVoidEvent,Set.mem_setOf_eq,not_forall,not_not] using hVoid
    apply le_antisymm (maximum_retainedAtTag_le t z)
    apply maximum_le _ (maximum_nonnegative _)
    intro i
    by_cases hi : taggedAbove t (z i)
    · have h := le_maximum (fun k => retainAboveTag t (z k)) i
      rwa [retainAboveTag,if_pos hi] at h
    · have hiLe : (z i).1≤t.1 := le_of_not_gt (fun h => hi (Or.inl h))
      have hjLe : t.1≤(z j).1 := hj.elim le_of_lt (fun h => h.1.le)
      calc
        (z i).1≤t.1 := hiLe
        _≤(z j).1 := hjLe
        _=retainAboveTag t (z j) := (if_pos hj).symm
        _≤maximum (fun k => retainAboveTag t (z k)) := le_maximum (fun k : Fin n => retainAboveTag t (z k)) j

/-- The numerical lower-fraction mean estimate, valid for every fixed cutoff
and the empty family as well as arbitrary numerical atoms. -/
theorem retainedAtTag_expectedMaximum_lower (P : Instance n)
    (hP : Integrable maximum P.valuesLaw) (t : ℝ × ℝ) :
    (1-P.taggedVoidProbability t)*P.expectedMaximum≤(P.retainedAtTag t).expectedMaximum := by
  let Z : (Fin n → ℝ × ℝ) → ℝ := fun z => maximum (fun i => (z i).1)
  let μ := P.taggedValuesLaw
  have hOrig := P.taggedValues_projection_measurePreserving
  have hZI : Integrable Z μ := hOrig.integrable_comp_of_integrable hP
  have hD := measurableSet_taggedVoidEvent (n:=n) t
  have hLow : ∀ z∈taggedVoidEvent (n:=n) t, Z z≤max 0 t.1 := by
    intro z hz
    apply maximum_le _ (le_max_left _ _)
    intro i
    exact (le_of_not_gt (fun h => hz i (Or.inl h))).trans (le_max_right _ _)
  have hHigh : ∀ z∉taggedVoidEvent (n:=n) t, max 0 t.1≤Z z := by
    intro z hz
    obtain ⟨j,hj⟩ : ∃ j, taggedAbove t (z j) := by
      simpa only [taggedVoidEvent,Set.mem_setOf_eq,not_forall,not_not] using hz
    apply max_le (maximum_nonnegative _)
    exact (hj.elim le_of_lt (fun h => h.1.le)).trans (le_maximum (fun i => (z i).1) j)
  have hSplit := ProphetSecretary.Probability.upper_split_integral_ge_probability_mul μ hZI hD
    (Eventually.of_forall hLow) (Eventually.of_forall hHigh)
  have hOriginalMean : (∫ z, Z z ∂μ)=P.expectedMaximum := by
    have h := integral_map (μ:=μ) hOrig.measurable.aemeasurable measurable_maximum.aestronglyMeasurable
    rw [hOrig.map_eq] at h
    exact h.symm
  have hRet := P.taggedRetainedValues_measurePreserving t
  have hRetainedMean : (P.retainedAtTag t).expectedMaximum=∫ z in (taggedVoidEvent t)ᶜ, Z z ∂μ := by
    have h := integral_map (μ:=μ) hRet.measurable.aemeasurable measurable_maximum.aestronglyMeasurable
    rw [hRet.map_eq] at h
    change (∫ x, maximum x ∂(P.retainedAtTag t).valuesLaw)=_
    rw [h]
    have hEq : (fun z => maximum (fun i => retainAboveTag t (z i)))=(taggedVoidEvent t)ᶜ.indicator Z := by
      funext z
      rw [maximum_retainedAtTag_eq]
      by_cases hz : z∈taggedVoidEvent t <;> simp only [hz,if_true,if_false,Set.indicator_apply,Set.mem_compl_iff,not_true_eq_false,not_false_eq_true,Z]
    rw [hEq,integral_indicator hD.compl]
  rw [P.taggedVoidEvent_probability t,hOriginalMean] at hSplit
  rwa [hRetainedMean]

end ProphetSecretary.Model.Instance
