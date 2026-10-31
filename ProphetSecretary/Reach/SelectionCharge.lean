import ProphetSecretary.Reach.CrossingAllocation
import ProphetSecretary.Reach.TailLifting
import ProphetSecretary.Probability.CandidateValue

/-!
# Charging continuous crossings to selection

Each fixed unseen state has a deterministic interior continuation root. An actual
pending path can meet at most one such root, because its acceptance gap strictly
increases with elapsed time. After a root, a reached candidate of that value is
accepted. Independent clock replacement then charges the disjoint crossing events
to the probability of selecting that candidate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- The root of a fixed unseen state lies in the interior horizon and is actually
visited by the pending candidate's unseen-state path. Candidate clocks are latent. -/
def Instance.InteriorCrossing (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin n) (z x : ℝ) (A : Finset (Fin n)) (u : Fin n → ℝ) : Prop :=
  i ∉ A ∧ optimalScalarValue (P.restrictTo A) 1 0 < x ∧
    (P.restrictTo A).durationRoot (P.restrictTo_integrable_maximum A hP) x < z ∧
      otherUnseen u i ((P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z x) = A

lemma Instance.InteriorCrossing.time_mem_Ioo (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {i : Fin n} {z x : ℝ} (hz : 0 < z)
    {A : Finset (Fin n)} {u : Fin n → ℝ} (h : P.InteriorCrossing hP i z x A u) :
    (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z x ∈ Ioo (0 : ℝ) 1 :=
  (P.restrictTo A).crossingTime_mem_Ioo (P.restrictTo_integrable_maximum A hP) hz h.2.1 h.2.2.1

lemma Instance.InteriorCrossing.gap_zero (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {i : Fin n} {z x : ℝ} (hz : 0 < z)
    {A : Finset (Fin n)} {u : Fin n → ℝ} (h : P.InteriorCrossing hP i z x A u) :
    P.candidateGap 1 z i x u
      ((P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z x) = 0 := by
  have ht := h.time_mem_Ioo P hP hz
  have he := (P.restrictTo A).value_at_crossingTime (P.restrictTo_integrable_maximum A hP) hz h.2.1
  unfold Instance.candidateGap
  rw [h.2.2.2, max_eq_right (sub_nonneg.mpr ht.2.le)]
  change 1 * x - optimalScalarValue (P.restrictTo A) 1 _ = 0
  rw [he]
  ring

lemma Instance.InteriorCrossing.unique (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {i : Fin n} {z x : ℝ} (hz : 0 < z)
    {A B : Finset (Fin n)} {u : Fin n → ℝ}
    (hA : P.InteriorCrossing hP i z x A u) (hB : P.InteriorCrossing hP i z x B u) : A = B := by
  let a := (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z x
  let b := (P.restrictTo B).crossingTime (P.restrictTo_integrable_maximum B hP) z x
  have ha := hA.time_mem_Ioo P hP hz
  have hb := hB.time_mem_Ioo P hP hz
  have hga := hA.gap_zero P hP hz
  have hgb := hB.gap_zero P hP hz
  have hslope := P.candidateGap_slope hP zero_lt_one hz.le i x u
  have heq : a = b := by
    have hpos : 0 < z / (4 * (1 + (n : ℝ))) := by positivity
    rcases le_total a b with hab | hba
    · have he := hslope a ⟨ha.1.le, ha.2.le⟩ b ⟨hb.1.le, hb.2.le⟩ hab
      change P.candidateGap 1 z i x u a = 0 at hga
      change P.candidateGap 1 z i x u b = 0 at hgb
      rw [hga, hgb] at he
      nlinarith
    · have he := hslope b ⟨hb.1.le, hb.2.le⟩ a ⟨ha.1.le, ha.2.le⟩ hba
      change P.candidateGap 1 z i x u a = 0 at hga
      change P.candidateGap 1 z i x u b = 0 at hgb
      rw [hga, hgb] at he
      nlinarith
  have hstateA : otherUnseen u i a = A := hA.2.2.2
  have hstateB : otherUnseen u i b = B := hB.2.2.2
  rw [heq] at hstateA
  exact hstateA.symm.trans hstateB

lemma Instance.InteriorCrossing.gap_nonnegative_after (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {i : Fin n} {z x : ℝ} (hz : 0 < z)
    {A : Finset (Fin n)} {u : Fin n → ℝ} (h : P.InteriorCrossing hP i z x A u)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hrs : (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z x ≤ s) :
    0 ≤ P.candidateGap 1 z i x u s := by
  have hr := h.time_mem_Ioo P hP hz
  have he := P.candidateGap_slope hP zero_lt_one hz.le i x u _ ⟨hr.1.le, hr.2.le⟩ s hs hrs
  rw [h.gap_zero P hP hz] at he
  have hnonneg : 0 ≤ z / (4 * (1 + (n : ℝ))) *
      (s - (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z x) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hrs)
  linarith

lemma Instance.InteriorCrossing.accepts_after (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {i : Fin n} {z a : ℝ} (hz : 0 < z)
    {A : Finset (Fin n)} {x u : Fin n → ℝ} (h : P.InteriorCrossing hP i z a A u)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hrs : (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z a ≤ s) :
    (P.valuePolicy hP zero_le_one hz.le).rule.action () Finset.univ
      (Function.update x i a) (Function.update u i s) i = true := by
  have hgap := h.gap_nonnegative_after P hP hz hs hrs
  let y := Function.update x i a
  have hy : y i = a := Function.update_self _ _ _
  have heq := P.candidateGap_eq_replacedAcceptanceGap 1 z i y u s
  rw [hy] at heq
  rw [heq] at hgap
  simp only [Policy.action, Instance.valuePolicy, thresholdPolicy, Function.update_self,
    decide_eq_true_eq, Instance.valueThreshold, div_one]
  simpa only [y, Instance.continuationAtArrival, Function.update_self, one_mul] using (sub_nonneg.mp hgap)

lemma Instance.measurableSet_interiorCrossing (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) (z x : ℝ) (A : Finset (Fin n)) :
    MeasurableSet {u : Fin n → ℝ | P.InteriorCrossing hP i z x A u} := by
  by_cases hi : i ∉ A
  · by_cases hx : optimalScalarValue (P.restrictTo A) 1 0 < x
    · by_cases hr : (P.restrictTo A).durationRoot (P.restrictTo_integrable_maximum A hP) x < z
      · simpa [Instance.InteriorCrossing, hi, hx, hr] using
          measurableSet_otherUnseen_eq A i hi ((P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z x)
      · simp [Instance.InteriorCrossing, hr]
    · simp [Instance.InteriorCrossing, hx]
  · simp [Instance.InteriorCrossing, hi]

lemma Instance.interiorCrossing_update_clock (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) (z x : ℝ) (A : Finset (Fin n))
    (u : Fin n → ℝ) (s : ℝ) :
    P.InteriorCrossing hP i z x A (Function.update u i s) ↔ P.InteriorCrossing hP i z x A u := by
  have he (r : ℝ) : otherUnseen (Function.update u i s) i r = otherUnseen u i r := by
    ext j
    by_cases hji : j = i
    · subst j; simp [otherUnseen]
    · simp [otherUnseen, hji]
  unfold Instance.InteriorCrossing
  rw [he]

lemma Instance.InteriorCrossing.selects_after (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {i : Fin n} {z a : ℝ} (hz : 0 < z)
    {A : Finset (Fin n)} {x u : Fin n → ℝ} (h : P.InteriorCrossing hP i z a A u)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hrs : (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z a ≤ s)
    (hsσ : s ≤ (P.valuePolicy hP zero_le_one hz.le).rule.pendingTime () x u i) :
    (P.valuePolicy hP zero_le_one hz.le).rule.Selects () Finset.univ
      (Function.update x i a) (Function.update u i s) i := by
  let π := (P.valuePolicy hP zero_le_one hz.le).rule
  have ha := h.accepts_after P hP hz (x := x) hs hrs
  have hr : π.Reaches () (Function.update x i a) (Function.update u i s) i := by
    apply (π.reaches_iff_le_pendingTime _ _ _ i (by simpa using hs.2)).mpr
    simpa only [Function.update_self, π.pendingTime_update] using hsσ
  have hacc : i ∈ π.accepted () Finset.univ (Function.update x i a) (Function.update u i s) :=
    (π.mem_accepted _ _ _ _ _).mpr ⟨Finset.mem_univ _, ha⟩
  exact ⟨hacc, le_antisymm hr (π.stoppingTime_le_of_accepted _ _ _ _ _ hacc)⟩

lemma sum_le_of_unique_event {ι : Type*} [Fintype ι] (E : ι → Prop) (f : ι → ℝ) {g : ℝ}
    (hg : 0 ≤ g) (hunique : ∀ a b, E a → E b → a = b) (hbound : ∀ a, E a → f a ≤ g) :
    (∑ a, if E a then f a else 0) ≤ g := by
  by_cases hex : ∃ a, E a
  · obtain ⟨a, ha⟩ := hex
    rw [Finset.sum_eq_single a]
    · simpa only [if_pos ha] using hbound a ha
    · intro b _ hba
      rw [if_neg (fun hb => hba (hunique b a hb ha))]
    · intro ha'
      exact False.elim (ha' (Finset.mem_univ a))
  · have hnone : ∀ a, ¬E a := fun a ha => hex ⟨a, ha⟩
    simpa only [if_neg (hnone _), Finset.sum_const_zero] using hg

/-- All visited roots are charged together to one candidate selection. This
pointwise inequality precedes integration over the fresh candidate clock. -/
lemma Instance.sum_crossing_reach_le_selection (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z a : ℝ} (hz : 0 < z)
    (x u : Fin n → ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hinj : Function.Injective (Function.update u i s)) :
    (∑ A : Finset (Fin n), if P.InteriorCrossing hP i z a A u then
      (if (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z a ≤ s ∧
        s ≤ (P.valuePolicy hP zero_le_one hz.le).rule.pendingTime () x u i then (1 : ℝ) else 0) else 0) ≤
      if (P.valuePolicy hP zero_le_one hz.le).rule.ActualSelects () Finset.univ
        (Function.update x i a) (Function.update u i s) i then 1 else 0 := by
  apply sum_le_of_unique_event
  · split_ifs <;> norm_num
  · intro A B hA hB
    exact hA.unique P hP hz hB
  · intro A hA
    split_ifs with htime hselect
    · exact le_refl _
    · have hsel := hA.selects_after P hP hz hs htime.1 htime.2
      exact False.elim (hselect (((P.valuePolicy hP zero_le_one hz.le).rule.actualSelects_iff_selects
        _ _ _ _ hinj i).mpr hsel))
    · exact zero_le_one
    · exact le_refl _

lemma uniformClock_integral_interval {r σ : ℝ} (hr0 : 0 ≤ r) (hσ1 : σ ≤ 1) :
    (∫ s, (if r ≤ s ∧ s ≤ σ then (1 : ℝ) else 0) ∂Instance.uniformClock) = max (σ - r) 0 := by
  have hf : (fun s : ℝ => if r ≤ s ∧ s ≤ σ then (1 : ℝ) else 0) = (Icc r σ).indicator 1 := by
    funext s
    simp [Set.indicator]
  have hset : Icc r σ ∩ Icc (0 : ℝ) 1 = Icc r σ := by
    ext s
    constructor
    · exact And.left
    · intro h
      exact ⟨h, hr0.trans h.1, h.2.trans hσ1⟩
  rw [hf, integral_indicator_one measurableSet_Icc, Measure.real, Instance.uniformClock,
    Measure.restrict_apply measurableSet_Icc, hset, Real.volume_Icc, ENNReal.toReal_ofReal']

/-- Conditional selection probability is evaluated with the original design rule
fixed, and only the executed candidate value replaced. -/
noncomputable def Instance.fixedValueSelectionProbability (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z) (a : ℝ) : ℝ :=
  ∫ ω : World n Unit, if (P.valuePolicy hP zero_le_one hz.le).rule.ActualSelects () Finset.univ
    (Function.update ω.1 i a) ω.2.1 i then 1 else 0 ∂P.worldLaw (Measure.dirac ())

noncomputable def Instance.crossingClockCharge (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z) (a : ℝ)
    (A : Finset (Fin n)) (v : World n Unit × ℝ) : ℝ :=
  if P.InteriorCrossing hP i z a A v.1.2.1 then
    (if (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z a ≤ v.2 ∧
      v.2 ≤ (P.valuePolicy hP zero_le_one hz.le).rule.pendingTime () v.1.1 v.1.2.1 i then 1 else 0) else 0

noncomputable def Instance.crossingDurationCharge (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z) (a : ℝ)
    (A : Finset (Fin n)) (ω : World n Unit) : ℝ :=
  if P.InteriorCrossing hP i z a A ω.2.1 then
    max ((P.valuePolicy hP zero_le_one hz.le).rule.pendingTime () ω.1 ω.2.1 i -
      (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z a) 0 else 0

lemma Instance.measurable_crossingClockCharge (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z) (a : ℝ)
    (A : Finset (Fin n)) : Measurable (P.crossingClockCharge hP i hz a A) := by
  have hclock : Measurable (fun v : World n Unit × ℝ => v.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hK := (P.measurableSet_interiorCrossing hP i z a A).preimage hclock
  have hσ : Measurable (fun v : World n Unit × ℝ => (P.valuePolicy hP zero_le_one hz.le).rule.pendingTime () v.1.1 v.1.2.1 i) := ((P.valuePolicy hP zero_le_one hz.le).rule.measurable_pendingWorldTime
    (P.valuePolicy hP zero_le_one hz.le).measurable_rule i).comp measurable_fst
  exact Measurable.ite hK (Measurable.ite
    ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd hσ))
      measurable_const measurable_const) measurable_const

lemma Instance.integrable_crossingClockCharge (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z) (a : ℝ)
    (A : Finset (Fin n)) : Integrable (P.crossingClockCharge hP i hz a A)
      ((P.worldLaw (Measure.dirac ())).prod Instance.uniformClock) := by
  apply Integrable.of_bound (P.measurable_crossingClockCharge hP i hz a A).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun v => by
    unfold Instance.crossingClockCharge
    split_ifs <;> norm_num

lemma Instance.integral_crossingClockCharge (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z) (a : ℝ)
    (A : Finset (Fin n)) :
    (∫ v, P.crossingClockCharge hP i hz a A v ∂(P.worldLaw (Measure.dirac ())).prod Instance.uniformClock) =
      ∫ ω, P.crossingDurationCharge hP i hz a A ω ∂P.worldLaw (Measure.dirac ()) := by
  rw [integral_prod _ (P.integrable_crossingClockCharge hP i hz a A)]
  apply integral_congr_ae
  filter_upwards [P.pendingTime_mem_unitInterval (Measure.dirac ()) (P.valuePolicy hP zero_le_one hz.le).rule i] with ω hω
  by_cases hK : P.InteriorCrossing hP i z a A ω.2.1
  · simp only [Instance.crossingClockCharge, if_pos hK, Instance.crossingDurationCharge]
    exact uniformClock_integral_interval (hK.time_mem_Ioo P hP hz).1.le hω.2
  · simp [Instance.crossingClockCharge, Instance.crossingDurationCharge, hK]

lemma Instance.expected_crossingDuration_le_fixed_selection (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z) (a : ℝ) :
    (∑ A : Finset (Fin n), ∫ ω, P.crossingDurationCharge hP i hz a A ω ∂P.worldLaw (Measure.dirac ())) ≤
      P.fixedValueSelectionProbability hP i hz a := by
  let π := (P.valuePolicy hP zero_le_one hz.le).rule
  let μ := P.worldLaw (Measure.dirac ())
  let f : World n Unit → ℝ := fun ω => if π.ActualSelects () Finset.univ (Function.update ω.1 i a) ω.2.1 i then 1 else 0
  have hm : Measurable f := Measurable.ite (π.measurableSet_actualSelects
    (P.valuePolicy hP zero_le_one hz.le).measurable_rule measurable_const
    (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ i) measurable_const measurable_const
  have hi : Integrable f μ := Integrable.of_bound hm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by dsimp [f]; split_ifs <;> norm_num)
  have hrep := P.replaceClock_measurePreserving (Measure.dirac ()) i
  have hir := hrep.integrable_comp_of_integrable hi
  have hsum : Integrable (fun v => ∑ A : Finset (Fin n), P.crossingClockCharge hP i hz a A v)
      (μ.prod Instance.uniformClock) := integrable_finsetSum _ (fun A _ => P.integrable_crossingClockCharge hP i hz a A)
  have hunit : ∀ᵐ v : World n Unit × ℝ ∂μ.prod Instance.uniformClock, v.2 ∈ Icc (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := Instance.uniformClock)).ae (ae_restrict_mem measurableSet_Icc)
  have hinj : ∀ᵐ v : World n Unit × ℝ ∂μ.prod Instance.uniformClock, Function.Injective (Function.update v.1.2.1 i v.2) :=
    hrep.quasiMeasurePreserving.ae (P.world_clocks_distinct (Measure.dirac ()))
  have hpoint : ∀ᵐ v ∂μ.prod Instance.uniformClock,
      (∑ A : Finset (Fin n), P.crossingClockCharge hP i hz a A v) ≤ f (Instance.replaceClock i v) := by
    filter_upwards [hunit, hinj] with v hv hinjv
    exact P.sum_crossing_reach_le_selection hP i hz v.1.1 v.1.2.1 hv hinjv
  calc
    _ = ∫ v, ∑ A : Finset (Fin n), P.crossingClockCharge hP i hz a A v ∂μ.prod Instance.uniformClock := by
      simp_rw [← P.integral_crossingClockCharge hP i hz a]
      exact (integral_finsetSum _ (fun A _ => P.integrable_crossingClockCharge hP i hz a A)).symm
    _ ≤ ∫ v, f (Instance.replaceClock i v) ∂μ.prod Instance.uniformClock := integral_mono_ae hsum hir hpoint
    _ = _ := by
      have he := integral_map (μ := μ.prod Instance.uniformClock) hrep.measurable.aemeasurable hm.aestronglyMeasurable
      rw [hrep.map_eq] at he
      exact he.symm

/-- The actual canonical child duration at a positive root coefficient, extended
by zero where no positive root exists. The derivative identity supplies measurability. -/
noncomputable def Instance.rootDuration (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (x : ℝ) : ℝ :=
  if 0 < P.durationRoot hP x then deriv (remainingScalarValue P 1 1) (P.durationRoot hP x) else 0

lemma Instance.rootDuration_eq_canonical (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {x : ℝ} (hd : 0 < P.durationRoot hP x) :
    P.rootDuration hP x =
      (P.valuePolicy hP zero_le_one (P.durationRoot_nonnegative hP x)).expectedDuration P := by
  rw [Instance.rootDuration, if_pos hd]
  simpa only [one_mul] using remainingScalarValue_deriv_eq_canonicalDuration P hP zero_lt_one zero_le_one hd

lemma Instance.measurable_rootDuration (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) : Measurable (P.rootDuration hP) := by
  have hm := (remainingScalarValue_deriv_continuousOn_all P hP zero_lt_one zero_le_one).measurable_piecewise
    (g := fun _ : ℝ => (0 : ℝ)) continuousOn_const measurableSet_Ioi
  exact hm.comp (P.measurable_durationRoot hP)

lemma Instance.rootDuration_mem_unitInterval (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (x : ℝ) : P.rootDuration hP x ∈ Icc (0 : ℝ) 1 := by
  by_cases hd : 0 < P.durationRoot hP x
  · rw [P.rootDuration_eq_canonical hP hd]
    exact ⟨RandomizedPolicy.expectedDuration_nonnegative _ _, RandomizedPolicy.expectedDuration_le_one _ _⟩
  · simp [Instance.rootDuration, hd]

noncomputable def Instance.crossingSelectionCharge (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z) (a : ℝ)
    (A : Finset (Fin n)) (ω : World n Unit) : ℝ :=
  if P.InteriorCrossing hP i z a A ω.2.1 ∧
      (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z a ≤
        (P.valuePolicy hP zero_le_one hz.le).rule.pendingTime () ω.1 ω.2.1 i then
    (1 - (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z a) ^ 2 *
      (P.restrictTo A).rootDuration (P.restrictTo_integrable_maximum A hP) a else 0

lemma Instance.measurable_crossingSelectionCharge (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z) (a : ℝ)
    (A : Finset (Fin n)) : Measurable (P.crossingSelectionCharge hP i hz a A) := by
  have hK := (P.measurableSet_interiorCrossing hP i z a A).preimage
    (measurable_fst.comp measurable_snd : Measurable (fun ω : World n Unit => ω.2.1))
  have hσ := (P.valuePolicy hP zero_le_one hz.le).rule.measurable_pendingWorldTime
    (P.valuePolicy hP zero_le_one hz.le).measurable_rule i
  exact Measurable.ite (hK.inter (measurableSet_le measurable_const hσ)) measurable_const measurable_const

lemma Instance.crossingSelectionCharge_mem_unitInterval (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z) (a : ℝ)
    (A : Finset (Fin n)) (ω : World n Unit) : P.crossingSelectionCharge hP i hz a A ω ∈ Icc (0 : ℝ) 1 := by
  unfold Instance.crossingSelectionCharge
  split_ifs with h
  · have hr := h.1.time_mem_Ioo P hP hz
    have hT := (P.restrictTo A).rootDuration_mem_unitInterval (P.restrictTo_integrable_maximum A hP) a
    constructor
    · exact mul_nonneg (sq_nonneg _) hT.1
    · have hu2 : (1 - (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z a) ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
      exact (mul_le_mul_of_nonneg_left hT.2 (sq_nonneg _)).trans (by simpa only [mul_one] using hu2)
  · exact ⟨le_refl _, zero_le_one⟩

lemma Instance.integrable_crossingSelectionCharge (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z) (a : ℝ)
    (A : Finset (Fin n)) : Integrable (P.crossingSelectionCharge hP i hz a A) (P.worldLaw (Measure.dirac ())) := by
  apply Integrable.of_bound (P.measurable_crossingSelectionCharge hP i hz a A).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun ω => by
    have h := P.crossingSelectionCharge_mem_unitInterval hP i hz a A ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

lemma Instance.expected_crossingSelection_le_duration (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z) (a : ℝ)
    (A : Finset (Fin n)) :
    (∫ ω, P.crossingSelectionCharge hP i hz a A ω ∂P.worldLaw (Measure.dirac ())) ≤
      ∫ ω, P.crossingDurationCharge hP i hz a A ω ∂P.worldLaw (Measure.dirac ()) := by
  by_cases hi : i ∉ A
  · by_cases hx : optimalScalarValue (P.restrictTo A) 1 0 < a
    · by_cases hd : (P.restrictTo A).durationRoot (P.restrictTo_integrable_maximum A hP) a < z
      · let Q := P.restrictTo A
        let hQ := P.restrictTo_integrable_maximum A hP
        let r := Q.crossingTime hQ z a
        let π := (P.valuePolicy hP zero_le_one hz.le).rule
        let σ := fun ω : World n Unit => π.pendingTime () ω.1 ω.2.1 i
        let S := {ω : World n Unit | otherUnseen ω.2.1 i r = A}
        let F := prefixSurvivalWeight π (fun _ => 1) i r
        let T := Q.rootDuration hQ a
        have ht : r ∈ Ioo (0 : ℝ) 1 := Q.crossingTime_mem_Ioo hQ hz hx hd
        have hS : MeasurableSet S := (measurableSet_otherUnseen_eq A i hi r).preimage
          (measurable_fst.comp measurable_snd)
        have hK (ω : World n Unit) : P.InteriorCrossing hP i z a A ω.2.1 ↔ ω ∈ S := by
          simp only [Instance.InteriorCrossing, hi, hx, hd, true_and, not_false_eq_true]
          rfl
        have hFnonneg (ω : World n Unit) : 0 ≤ F ω := by
          dsimp [F, prefixSurvivalWeight]
          split_ifs <;> norm_num
        have hmass : 0 ≤ ∫ ω in S, F ω ∂P.worldLaw (Measure.dirac ()) := integral_nonneg hFnonneg
        have hT : T ∈ Icc (0 : ℝ) 1 := Q.rootDuration_mem_unitInterval hQ a
        have hTeq : T = (Q.valuePolicy hQ zero_le_one (Q.durationRoot_nonnegative hQ a)).expectedDuration Q :=
          Q.rootDuration_eq_canonical hQ (Q.durationRoot_positive hQ hx)
        have halloc := P.survival_allocation_at_crossing hP (Measure.dirac ()) A i hi hz hx hd
          (fun _ => (1 : ℝ)) measurable_const (K := 1) (fun _ => ⟨zero_le_one, le_refl _⟩)
        change (1 - r) * (Q.valuePolicy hQ zero_le_one (Q.durationRoot_nonnegative hQ a)).expectedDuration Q *
          (∫ ω in S, F ω ∂P.worldLaw (Measure.dirac ())) ≤
          ∫ ω in S, F ω * (∫ s in Icc r (1 : ℝ), if s ≤ σ ω then (1 : ℝ) else 0) ∂P.worldLaw (Measure.dirac ()) at halloc
        rw [← hTeq] at halloc
        have halloc' : (1 - r) * T * (∫ ω in S, F ω ∂P.worldLaw (Measure.dirac ())) ≤
            ∫ ω in S, F ω * (σ ω - r) ∂P.worldLaw (Measure.dirac ()) := by
          convert halloc using 1
          exact (integral_congr_ae (Filter.Eventually.of_forall fun ω => prefixSurvivalWeight_mul_integral π (fun _ => 1) i r ω)).symm
        have hcharge : (∫ ω, P.crossingSelectionCharge hP i hz a A ω ∂P.worldLaw (Measure.dirac ())) =
            (1 - r) ^ 2 * T * ∫ ω in S, F ω ∂P.worldLaw (Measure.dirac ()) := by
          rw [← integral_const_mul, ← integral_indicator hS]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by
            have hk := hK ω
            have hseed : ω.2.2 = () := Subsingleton.elim _ _
            simp only [Set.indicator_apply, F, prefixSurvivalWeight, one_mul, hseed]
            change (if P.InteriorCrossing hP i z a A ω.2.1 ∧ r ≤ σ ω then (1 - r) ^ 2 * T else 0) =
              (if ω ∈ S then (1 - r) ^ 2 * T * (if r ≤ σ ω then 1 else 0) else 0)
            by_cases he : ω ∈ S
            · have hc := hk.mpr he
              by_cases hs : r ≤ σ ω <;> simp [hc, he, hs]
            · have hc := mt hk.mp he
              simp [hc, he]
        have hduration : (∫ ω, P.crossingDurationCharge hP i hz a A ω ∂P.worldLaw (Measure.dirac ())) =
            ∫ ω in S, F ω * (σ ω - r) ∂P.worldLaw (Measure.dirac ()) := by
          rw [← integral_indicator hS]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by
            have hk := hK ω
            have hseed : ω.2.2 = () := Subsingleton.elim _ _
            simp only [Set.indicator_apply, F, prefixSurvivalWeight, one_mul, hseed]
            change (if P.InteriorCrossing hP i z a A ω.2.1 then max (σ ω - r) 0 else 0) =
              (if ω ∈ S then (if r ≤ σ ω then 1 else 0) * (σ ω - r) else 0)
            by_cases he : ω ∈ S
            · have hc := hk.mpr he
              by_cases hs : r ≤ σ ω
              · simp only [if_pos hc, if_pos he, if_pos hs, one_mul, max_eq_left (sub_nonneg.mpr hs)]
              · simp only [if_pos hc, if_pos he, if_neg hs, zero_mul, max_eq_right (sub_nonpos.mpr (le_of_not_ge hs))]
            · have hc := mt hk.mp he
              simp [hc, he]
        rw [hcharge, hduration]
        have hu : (1 - r) ^ 2 ≤ 1 - r := by nlinarith [ht.1, ht.2]
        exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu hT.1) hmass).trans halloc'
      · simp [Instance.crossingSelectionCharge, Instance.crossingDurationCharge, Instance.InteriorCrossing, hd]
    · simp [Instance.crossingSelectionCharge, Instance.crossingDurationCharge, Instance.InteriorCrossing, hx]
  · simp [Instance.crossingSelectionCharge, Instance.crossingDurationCharge, Instance.InteriorCrossing, hi]

/-- `eq:ps-curvature-selection-charge`, summed over the disjoint finite unseen
states for a fixed candidate value. The canonical rule retains its original law. -/
lemma Instance.expected_crossingSelection_le_fixed_selection (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z) (a : ℝ) :
    (∑ A : Finset (Fin n), ∫ ω, P.crossingSelectionCharge hP i hz a A ω ∂P.worldLaw (Measure.dirac ())) ≤
      P.fixedValueSelectionProbability hP i hz a :=
  (Finset.sum_le_sum fun A _ => P.expected_crossingSelection_le_duration hP i hz a A).trans
    (P.expected_crossingDuration_le_fixed_selection hP i hz a)

lemma measurable_otherUnseen_joint (i : Fin n) :
    Measurable (fun v : (Fin n → ℝ) × ℝ => otherUnseen v.1 i v.2) := by
  rw [measurable_finset_iff]
  intro j
  apply measurableSet_setOf.mp
  by_cases hji : j = i
  · subst j
    simp only [otherUnseen, Finset.mem_filter, Finset.mem_erase, ne_eq, not_true_eq_false,
      Finset.mem_univ, and_true, false_and, setOf_false]
    exact MeasurableSet.empty
  · simp only [otherUnseen, Finset.mem_filter, Finset.mem_erase, hji, not_false_eq_true,
      Finset.mem_univ, ne_eq, and_self, true_and]
    exact measurableSet_le measurable_snd ((measurable_pi_apply j).comp measurable_fst)

lemma Instance.measurableSet_interiorCrossing_joint (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) (z : ℝ) (A : Finset (Fin n)) :
    MeasurableSet {v : World n Unit × ℝ | P.InteriorCrossing hP i z v.2 A v.1.2.1} := by
  by_cases hi : i ∉ A
  · let Q := P.restrictTo A
    let hQ := P.restrictTo_integrable_maximum A hP
    have hd : Measurable (fun v : World n Unit × ℝ => Q.durationRoot hQ v.2) :=
      (Q.measurable_durationRoot hQ).comp measurable_snd
    have hr : Measurable (fun v : World n Unit × ℝ => Q.crossingTime hQ z v.2) :=
      measurable_const.sub (hd.div_const z)
    have hu : Measurable (fun v : World n Unit × ℝ => v.1.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_fst)
    have hstate := (measurable_otherUnseen_joint i).comp (hu.prodMk hr)
    have hstateEq := hstate (measurableSet_singleton A)
    have hcond : MeasurableSet {v : World n Unit × ℝ | optimalScalarValue Q 1 0 < v.2 ∧
        Q.durationRoot hQ v.2 < z ∧ otherUnseen v.1.2.1 i (Q.crossingTime hQ z v.2) = A} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        ((measurableSet_lt hd measurable_const).inter hstateEq)
    simpa only [Instance.InteriorCrossing, hi, not_false_eq_true, true_and] using hcond
  · simp [Instance.InteriorCrossing, hi]

lemma Instance.measurable_crossingSelectionCharge_joint (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z)
    (A : Finset (Fin n)) :
    Measurable (fun v : World n Unit × ℝ => P.crossingSelectionCharge hP i hz v.2 A v.1) := by
  let Q := P.restrictTo A
  let hQ := P.restrictTo_integrable_maximum A hP
  have hr : Measurable (fun v : World n Unit × ℝ => Q.crossingTime hQ z v.2) :=
    measurable_const.sub (((Q.measurable_durationRoot hQ).comp measurable_snd).div_const z)
  have hT : Measurable (fun v : World n Unit × ℝ => Q.rootDuration hQ v.2) :=
    (Q.measurable_rootDuration hQ).comp measurable_snd
  have hσ : Measurable (fun v : World n Unit × ℝ =>
      (P.valuePolicy hP zero_le_one hz.le).rule.pendingTime () v.1.1 v.1.2.1 i) :=
    ((P.valuePolicy hP zero_le_one hz.le).rule.measurable_pendingWorldTime
      (P.valuePolicy hP zero_le_one hz.le).measurable_rule i).comp measurable_fst
  exact Measurable.ite ((P.measurableSet_interiorCrossing_joint hP i z A).inter (measurableSet_le hr hσ))
    (((measurable_const.sub hr).pow_const 2).mul hT) measurable_const

lemma Instance.integrable_crossingSelectionCharge_joint (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z)
    (A : Finset (Fin n)) :
    Integrable (fun v : World n Unit × ℝ => P.crossingSelectionCharge hP i hz v.2 A v.1)
      ((P.worldLaw (Measure.dirac ())).prod (P.law i)) := by
  apply Integrable.of_bound (P.measurable_crossingSelectionCharge_joint hP i hz A).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun v => by
    have h := P.crossingSelectionCharge_mem_unitInterval hP i hz v.2 A v.1
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

lemma Instance.measurable_mean_crossingSelectionCharge (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z)
    (A : Finset (Fin n)) :
    Measurable (fun a => ∫ ω, P.crossingSelectionCharge hP i hz a A ω ∂P.worldLaw (Measure.dirac ())) :=
  (P.measurable_crossingSelectionCharge_joint hP i hz A).stronglyMeasurable.integral_prod_left'.measurable

lemma Instance.integrable_mean_crossingSelectionCharge (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z)
    (A : Finset (Fin n)) :
    Integrable (fun a => ∫ ω, P.crossingSelectionCharge hP i hz a A ω ∂P.worldLaw (Measure.dirac ())) (P.law i) :=
  (P.integrable_crossingSelectionCharge_joint hP i hz A).integral_prod_right

/-- The finite universal crossing charge has total mass at most one. The root
state family is summed before conditioning is removed; no instance-size factor
appears. The analytical complete offer vector is never supplied to the policy. -/
lemma Instance.total_crossingSelectionCharge_le_one (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 < z) :
    (∑ i : Fin n, ∫ a, ∑ A : Finset (Fin n),
      ∫ ω, P.crossingSelectionCharge hP i hz a A ω ∂P.worldLaw (Measure.dirac ()) ∂P.law i) ≤ 1 := by
  let π := (P.valuePolicy hP zero_le_one hz.le).rule
  have hπ : π.IsMeasurable := (P.valuePolicy hP zero_le_one hz.le).measurable_rule
  have hfixed (i : Fin n) (a : ℝ) : P.fixedValueSelectionProbability hP i hz a =
      π.selectionProbabilityAtValue P (Measure.dirac ()) i a := rfl
  have hbound (i : Fin n) :
      (∫ a, ∑ A : Finset (Fin n), ∫ ω, P.crossingSelectionCharge hP i hz a A ω
        ∂P.worldLaw (Measure.dirac ()) ∂P.law i) ≤ π.selectionProbability P (Measure.dirac ()) i := by
    have hmean : Integrable (fun a => ∑ A : Finset (Fin n),
        ∫ ω, P.crossingSelectionCharge hP i hz a A ω ∂P.worldLaw (Measure.dirac ())) (P.law i) :=
      integrable_finsetSum _ (fun A _ => P.integrable_mean_crossingSelectionCharge hP i hz A)
    have hsel := π.integrable_selectionProbabilityAtValue hπ P (Measure.dirac ()) i
    have hp := integral_mono hmean hsel (fun a => by
      rw [← hfixed]
      exact P.expected_crossingSelection_le_fixed_selection hP i hz a)
    rwa [π.integral_selectionProbabilityAtValue hπ P (Measure.dirac ()) i] at hp
  exact (Finset.sum_le_sum fun i _ => hbound i).trans (π.selectionProbability_sum_le_one hπ P (Measure.dirac ()))

end ProphetSecretary.Model
