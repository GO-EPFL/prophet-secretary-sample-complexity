import ProphetSecretary.Limiting.CountableConditionalDuration
import ProphetSecretary.Limiting.CountableDurationValueMonotonicity
import ProphetSecretary.Limiting.CountableValueDecision
import ProphetSecretary.Limiting.FirstAcceptanceTimeScaling
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuous canonical conditional duration

For fixed other observations, changing Xi affects only its own action. Away
from its random acceptance threshold that action is locally constant, hence
so is the actual duration. The already proved null clock level sets apply to
each fixed real value. Bounded dominated convergence gives continuity of the
conditional mean, including null support endpoints and value zero.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

lemma countableMarkovRule_codeAccepted_congr_of_own_action
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (i : ℕ) (v : CompleteWorld Seed) (a b : ℝ)
    (hOwn : (countableMarkovRule accept).candidateAction (replaceIndividualValue i (v,a)) (Sum.inl i)=
      (countableMarkovRule accept).candidateAction (replaceIndividualValue i (v,b)) (Sum.inl i)) (k : ℕ) :
    (countableMarkovRule accept).codeAccepted (replaceIndividualValue i (v,a)) k ↔
      (countableMarkovRule accept).codeAccepted (replaceIndividualValue i (v,b)) k := by
  by_cases hk : k=candidateEnumeration (Sum.inl i)
  · subst k
    have hTime : codeTime (replaceIndividualValue i (v,a)) (candidateEnumeration (Sum.inl i))=
        codeTime (replaceIndividualValue i (v,b)) (candidateEnumeration (Sum.inl i)) :=
      (codeTime_replaceIndividualValue i (v,a) _).trans (codeTime_replaceIndividualValue i (v,b) _).symm
    simp only [CountableRule.codeAccepted,codePresent,Equiv.symm_apply_apply,candidatePresent,hTime,hOwn]
  · exact (countableMarkovRule_codeAccepted_replaceValue_of_ne accept i (v,a) k hk).trans
      (countableMarkovRule_codeAccepted_replaceValue_of_ne accept i (v,b) k hk).symm

lemma countableMarkovRule_duration_eq_of_own_action
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (i : ℕ) (v : CompleteWorld Seed) (a b : ℝ)
    (hOwn : (countableMarkovRule accept).candidateAction (replaceIndividualValue i (v,a)) (Sum.inl i)=
      (countableMarkovRule accept).candidateAction (replaceIndividualValue i (v,b)) (Sum.inl i)) :
    (countableMarkovRule accept).realizedDuration (replaceIndividualValue i (v,a))=
      (countableMarkovRule accept).realizedDuration (replaceIndividualValue i (v,b)) := by
  have hA (k : ℕ) := (countableMarkovRule_codeAccepted_congr_of_own_action accept i v a b hOwn k).symm
  have hTime (k : ℕ) (_hk : (countableMarkovRule accept).codeAccepted (replaceIndividualValue i (v,a)) k) :
      codeTime (replaceIndividualValue i (v,b)) k=(1 : ℝ)*codeTime (replaceIndividualValue i (v,a)) k := by
    rw [one_mul]
    exact (codeTime_replaceIndividualValue i (v,b) k).trans (codeTime_replaceIndividualValue i (v,a) k).symm
  have h := FirstAcceptance.stoppingTimeAt_timeScale (h := (1 : ℝ)) zero_lt_one hA hTime
  change (countableMarkovRule accept).realizedDuration (replaceIndividualValue i (v,b))=
    (1 : ℝ)*(countableMarkovRule accept).realizedDuration (replaceIndividualValue i (v,a)) at h
  simpa only [one_mul] using h.symm

lemma canonical_individualActionAtValue_iff (B : CountableInstance) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ) (v : CompleteWorld Unit) (x : ℝ) (ht : v.2.2.1 i < 1) :
    (B.valueRule w c).candidateAction (replaceIndividualValue i (v,x)) (Sum.inl i)=true ↔
      B.clockProfile v.2.2.1 (some i) w c (v.2.2.1 i) ≤ w*x := by
  have h := B.valueRule_candidateAction_iff_preterminal hw hc (replaceIndividualValue i (v,x)) (Sum.inl i) ht
  rw [B.valueContinuationAtCandidate_eq_clockProfile] at h
  simpa only [replaceIndividualValue,candidatePoint,Function.update_self,candidateKind] using h

lemma canonical_durationAtValue_eventually_eq (B : CountableInstance) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ) (v : CompleteWorld Unit) (x₀ : ℝ)
    (ht : v.2.2.1 i < 1)
    (hLevel : B.clockProfile v.2.2.1 (some i) w c (v.2.2.1 i) ≠ w*x₀) :
    ∀ᶠ x in 𝓝 x₀, (B.valueRule w c).durationAtValue i (v,x)=(B.valueRule w c).durationAtValue i (v,x₀) := by
  let L := B.clockProfile v.2.2.1 (some i) w c (v.2.2.1 i)
  have hIff (x : ℝ) := B.canonical_individualActionAtValue_iff hw hc i v x ht
  have hMul : Continuous (fun x : ℝ => w*x) := continuous_const.mul continuous_id
  have hOwn : ∀ᶠ x in 𝓝 x₀,
      (B.valueRule w c).candidateAction (replaceIndividualValue i (v,x)) (Sum.inl i)=
        (B.valueRule w c).candidateAction (replaceIndividualValue i (v,x₀)) (Sum.inl i) := by
    by_cases hL : L ≤ w*x₀
    · have hStrict : L < w*x₀ := lt_of_le_of_ne hL hLevel
      filter_upwards [(hMul.tendsto x₀).eventually (lt_mem_nhds hStrict)] with x hx
      exact ((hIff x).mpr hx.le).trans ((hIff x₀).mpr hL).symm
    · have hStrict : w*x₀ < L := lt_of_not_ge hL
      filter_upwards [(hMul.tendsto x₀).eventually (gt_mem_nhds hStrict)] with x hx
      have hFalse : (B.valueRule w c).candidateAction (replaceIndividualValue i (v,x)) (Sum.inl i)=false := by
        cases hA : (B.valueRule w c).candidateAction (replaceIndividualValue i (v,x)) (Sum.inl i) with
        | false => rfl
        | true => exact False.elim ((not_le.mpr hx) ((hIff x).mp hA))
      have hFalse₀ : (B.valueRule w c).candidateAction (replaceIndividualValue i (v,x₀)) (Sum.inl i)=false := by
        cases hA : (B.valueRule w c).candidateAction (replaceIndividualValue i (v,x₀)) (Sum.inl i) with
        | false => rfl
        | true => exact False.elim (hL ((hIff x₀).mp hA))
      exact hFalse.trans hFalse₀.symm
  filter_upwards [hOwn] with x hx
  change (B.valueRule w c).realizedDuration (replaceIndividualValue i (v,x))=
    (B.valueRule w c).realizedDuration (replaceIndividualValue i (v,x₀))
  rw [B.valueRule_eq_markovAcceptance] at hx ⊢
  exact countableMarkovRule_duration_eq_of_own_action _ i v x x₀ hx

lemma canonical_durationAtValue_continuousAt (B : CountableInstance) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ) (v : CompleteWorld Unit) (x₀ : ℝ)
    (ht : v.2.2.1 i < 1)
    (hLevel : B.clockProfile v.2.2.1 (some i) w c (v.2.2.1 i) ≠ w*x₀) :
    ContinuousAt (fun x => (B.valueRule w c).durationAtValue i (v,x)) x₀ := by
  have hConst : Tendsto (fun _ : ℝ => (B.valueRule w c).durationAtValue i (v,x₀)) (𝓝 x₀)
      (𝓝 ((B.valueRule w c).durationAtValue i (v,x₀))) := tendsto_const_nhds
  apply hConst.congr'
  filter_upwards [B.canonical_durationAtValue_eventually_eq hw hc i v x₀ ht hLevel] with x hx
  exact hx.symm

theorem canonical_conditionalDurationAtValue_continuous (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (i : ℕ) :
    Continuous ((B.valueRule w c).conditionalDurationAtValue B (Measure.dirac ()) i) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let π := B.valueRule w c
  have hπ : π.IsMeasurable := B.valueRule_isMeasurable hw.le hc.le
  have hPoint : ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()),
      ContinuousAt (fun x => π.durationAtValue i (v,x)) x₀ := by
    have hLevel := (B.individualClocks_completeWorld_measurePreserving (Measure.dirac ())).quasiMeasurePreserving.ae
      (B.clockProfile_at_own_clock_ne_ae hZero i hw hc (w*x₀))
    filter_upwards [hLevel,B.present_candidate_times_mem_Ioo (Measure.dirac ())] with v hv ht
    exact B.canonical_durationAtValue_continuousAt hw hc i v x₀ (ht (Sum.inl i) trivial).2 hv
  change Tendsto (fun x => ∫ v, π.durationAtValue i (v,x) ∂B.completeWorldLaw (Measure.dirac ())) (𝓝 x₀)
    (𝓝 (∫ v, π.durationAtValue i (v,x₀) ∂B.completeWorldLaw (Measure.dirac ())))
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : CompleteWorld Unit => (1 : ℝ))
  · exact Eventually.of_forall (fun x => ((π.measurable_durationAtValue hπ i).comp
      (measurable_id.prodMk (measurable_const (a := x)))).aestronglyMeasurable)
  · exact Eventually.of_forall (fun x => Eventually.of_forall (fun v => by
      change ‖π.realizedDuration (replaceIndividualValue i (v,x))‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (π.duration_bounds _).1]
      exact (π.duration_bounds _).2))
  · exact integrable_const 1
  · exact hPoint

end ProphetSecretary.Limiting.CountableInstance
