import ProphetSecretary.Stability.OutcomeBounds

/-!
# Stability of selected occurrence tags

The common tag assignment is an analytical function of the complete experiment. Its
measurability and bounds are explicit; it adds no observations to either policy.
The finite comparison underlying paper `cor:selected-occurrence` uses independent
offers and clocks, without conditioning on survival.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed Seed' : Type*}

/-- The selected occurrence's tag, with zero on no selection. -/
noncomputable def Policy.selectedTag (π : Policy Seed n) (r : Seed)
    (x u a : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if π.ActualSelects r Finset.univ x u i then a i else 0

lemma Policy.selectedTag_eq_of_actualSelects (π : Policy Seed n) (r : Seed)
    (x u a : Fin n → ℝ) {i : Fin n} (hi : π.ActualSelects r Finset.univ x u i) :
    π.selectedTag r x u a = a i := by
  unfold Policy.selectedTag
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hji
    have hj : ¬π.ActualSelects r Finset.univ x u j :=
      fun hj => hji (π.actualSelects_unique r Finset.univ x u hj hi)
    simp [hj]
  · simp

lemma Policy.selectedTag_eq_zero_of_no_selection (π : Policy Seed n) (r : Seed)
    (x u a : Fin n → ℝ) (h : ∀ i, ¬π.ActualSelects r Finset.univ x u i) :
    π.selectedTag r x u a = 0 := by simp [Policy.selectedTag, h]

lemma Policy.selectedTag_abs_le (π : Policy Seed n) (r : Seed)
    (x u a : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B) (ha : ∀ i, |a i| ≤ B) :
    |π.selectedTag r x u a| ≤ B := by
  by_cases h : ∃ i, π.ActualSelects r Finset.univ x u i
  · obtain ⟨i, hi⟩ := h
    rw [π.selectedTag_eq_of_actualSelects r x u a hi]
    exact ha i
  · rw [π.selectedTag_eq_zero_of_no_selection r x u a (by simpa using h)]
    simpa using hB

/-- Two positive offers occur within the specified physical time separation. -/
def closePositivePair (b η : ℝ) (x u : Fin n → ℝ) : Prop :=
  ∃ i j, i ≠ j ∧ b < x i ∧ b < x j ∧ |u i - u j| ≤ η

/-- Distinct tags force a reward discrepancy, a duration discrepancy, or an
unconditioned pair of distinct positive offers with nearby clocks. `ActualSelects`
is literally unique, so this statement also handles clock ties. -/
lemma Policy.selectedTag_ne_implies (π : Policy Seed n) (ρ : Policy Seed' n)
    (r : Seed) (s : Seed') (x u a : Fin n → ℝ) {b η : ℝ}
    (hb : 0 < b) (hzero : ∀ i, x i < b → a i = 0)
    (hne : π.selectedTag r x u a ≠ ρ.selectedTag s x u a) :
    b / 2 ≤ |π.reward r Finset.univ x u - ρ.reward s Finset.univ x u| ∨
    η ≤ |π.stoppingTime r Finset.univ x u - ρ.stoppingTime s Finset.univ x u| ∨
    closePositivePair (b / 2) η x u := by
  by_cases hp : ∃ i, π.ActualSelects r Finset.univ x u i
  · obtain ⟨i, hi⟩ := hp
    rw [π.selectedTag_eq_of_actualSelects r x u a hi] at hne
    by_cases hq : ∃ j, ρ.ActualSelects s Finset.univ x u j
    · obtain ⟨j, hj⟩ := hq
      rw [ρ.selectedTag_eq_of_actualSelects s x u a hj] at hne
      have hij : i ≠ j := fun h => hne (congrArg a h)
      have hhigh : b ≤ x i ∨ b ≤ x j := by
        by_contra h
        push Not at h
        exact hne ((hzero i h.1).trans (hzero j h.2).symm)
      by_cases hR : b / 2 ≤ |π.reward r Finset.univ x u - ρ.reward s Finset.univ x u|
      · exact Or.inl hR
      by_cases hT : η ≤ |π.stoppingTime r Finset.univ x u - ρ.stoppingTime s Finset.univ x u|
      · exact Or.inr (Or.inl hT)
      apply Or.inr ∘ Or.inr
      rw [π.reward_eq_of_actualSelects r Finset.univ x u hi,
        ρ.reward_eq_of_actualSelects s Finset.univ x u hj] at hR
      have habs := abs_lt.mp (lt_of_not_ge hR)
      have hix : b / 2 < x i := by rcases hhigh with h | h <;> linarith
      have hjx : b / 2 < x j := by rcases hhigh with h | h <;> linarith
      exact ⟨i, j, hij, hix, hjx, by
        rw [← hi.1.2, ← hj.1.2] at hT
        exact (lt_of_not_ge hT).le⟩
    · have hz := ρ.selectedTag_eq_zero_of_no_selection s x u a (by simpa using hq)
      rw [hz] at hne
      have hix : b ≤ x i := le_of_not_gt (fun h => hne (hzero i h))
      rw [π.reward_eq_of_actualSelects r Finset.univ x u hi,
        ρ.reward_eq_zero_of_no_actualSelection s Finset.univ x u (by simpa using hq)]
      exact Or.inl (by rw [sub_zero, abs_of_pos (hb.trans_le hix)]; linarith)
  · have hz := π.selectedTag_eq_zero_of_no_selection r x u a (by simpa using hp)
    rw [hz] at hne
    by_cases hq : ∃ j, ρ.ActualSelects s Finset.univ x u j
    · obtain ⟨j, hj⟩ := hq
      rw [ρ.selectedTag_eq_of_actualSelects s x u a hj] at hne
      have hjx : b ≤ x j := le_of_not_gt (fun h => hne (hzero j h).symm)
      rw [π.reward_eq_zero_of_no_actualSelection r Finset.univ x u (by simpa using hp),
        ρ.reward_eq_of_actualSelects s Finset.univ x u hj]
      exact Or.inl (by rw [zero_sub, abs_neg, abs_of_pos (hb.trans_le hjx)]; linarith)
    · exact False.elim (hne (ρ.selectedTag_eq_zero_of_no_selection s x u a (by simpa using hq)).symm)

lemma Policy.selectedTag_difference_le (π : Policy Seed n) (ρ : Policy Seed' n)
    (r : Seed) (s : Seed') (x u a : Fin n → ℝ) {B b η : ℝ}
    (hB : 0 ≤ B) (hb : 0 < b) (hη : 0 < η)
    (ha : ∀ i, |a i| ≤ B) (hzero : ∀ i, x i < b → a i = 0) :
    |π.selectedTag r x u a - ρ.selectedTag s x u a| ≤
      2 * B * (2 * |π.reward r Finset.univ x u - ρ.reward s Finset.univ x u| / b +
        |π.stoppingTime r Finset.univ x u - ρ.stoppingTime s Finset.univ x u| / η +
        if closePositivePair (b / 2) η x u then 1 else 0) := by
  have hR : 0 ≤ 2 * |π.reward r Finset.univ x u - ρ.reward s Finset.univ x u| / b := by positivity
  have hT : 0 ≤ |π.stoppingTime r Finset.univ x u - ρ.stoppingTime s Finset.univ x u| / η := by positivity
  have hI : (0 : ℝ) ≤ if closePositivePair (b / 2) η x u then 1 else 0 := by split_ifs <;> norm_num
  by_cases heq : π.selectedTag r x u a = ρ.selectedTag s x u a
  · rw [heq, sub_self, abs_zero]
    positivity
  have hbound : |π.selectedTag r x u a - ρ.selectedTag s x u a| ≤ 2 * B := by
    calc
      _ ≤ |π.selectedTag r x u a| + |ρ.selectedTag s x u a| := abs_sub _ _
      _ ≤ B + B := add_le_add (π.selectedTag_abs_le r x u a hB ha) (ρ.selectedTag_abs_le s x u a hB ha)
      _ = _ := by ring
  have hcost : 1 ≤ 2 * |π.reward r Finset.univ x u - ρ.reward s Finset.univ x u| / b +
      |π.stoppingTime r Finset.univ x u - ρ.stoppingTime s Finset.univ x u| / η +
      if closePositivePair (b / 2) η x u then 1 else 0 := by
    rcases π.selectedTag_ne_implies ρ r s x u a (η := η) hb hzero heq with h | h | h
    · have := (le_div_iff₀ hb).mpr (show 1 * b ≤ 2 * |π.reward r Finset.univ x u - ρ.reward s Finset.univ x u| by linarith)
      linarith
    · have := (le_div_iff₀ hη).mpr (show 1 * η ≤ |π.stoppingTime r Finset.univ x u - ρ.stoppingTime s Finset.univ x u| by linarith)
      linarith
    · simp only [h, ite_true]
      linarith
  exact hbound.trans (by nlinarith)

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]

lemma Policy.measurable_selectedTag (π : Policy Seed n) (hπ : π.IsMeasurable)
    {r : Ω → Seed} {x u a : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ i, Measurable fun ω => x ω i) (hu : ∀ i, Measurable fun ω => u ω i)
    (ha : ∀ i, Measurable fun ω => a ω i) :
    Measurable fun ω => π.selectedTag (r ω) (x ω) (u ω) (a ω) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (π.measurableSet_actualSelects hπ hr hx hu Finset.univ i) (ha i) measurable_const

lemma measurableSet_closePositivePair {x u : Ω → Fin n → ℝ}
    (hx : ∀ i, Measurable fun ω => x ω i) (hu : ∀ i, Measurable fun ω => u ω i)
    (b η : ℝ) : MeasurableSet {ω | closePositivePair b η (x ω) (u ω)} := by
  simp only [closePositivePair, setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.inter (show MeasurableSet {ω : Ω | i ≠ j} by by_cases h : i ≠ j <;> simp [h])
  exact (measurableSet_lt measurable_const (hx i)).inter
    ((measurableSet_lt measurable_const (hx j)).inter
      (measurableSet_le (continuous_abs.measurable.comp ((hu i).sub (hu j))) measurable_const))

/-- Bounded measurable analytical tags give integrable selected tags. -/
lemma Policy.integrable_selectedTag (π : Policy Seed n) (hπ : π.IsMeasurable)
    (μ : Measure Ω) [IsFiniteMeasure μ] {r : Ω → Seed} {x u a : Ω → Fin n → ℝ}
    (hr : Measurable r) (hx : ∀ i, Measurable fun ω => x ω i)
    (hu : ∀ i, Measurable fun ω => u ω i) (ha : ∀ i, Measurable fun ω => a ω i)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ ω ∂μ, ∀ i, |a ω i| ≤ B) :
    Integrable (fun ω => π.selectedTag (r ω) (x ω) (u ω) (a ω)) μ := by
  apply Integrable.of_bound (π.measurable_selectedTag hπ hr hx hu ha).aestronglyMeasurable B
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs] using π.selectedTag_abs_le (r ω) (x ω) (u ω) (a ω) hB hω

/-- Integrable analytical scores can be multiplied by a bounded selected tag.
The score is permitted to inspect the complete offer vector. -/
lemma Policy.integrable_score_selectedTag (π : Policy Seed n) (hπ : π.IsMeasurable)
    (μ : Measure Ω) {Z : Ω → ℝ} (hZ : Integrable Z μ)
    {r : Ω → Seed} {x u a : Ω → Fin n → ℝ}
    (hr : Measurable r) (hx : ∀ i, Measurable fun ω => x ω i)
    (hu : ∀ i, Measurable fun ω => u ω i) (ha : ∀ i, Measurable fun ω => a ω i)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ ω ∂μ, ∀ i, |a ω i| ≤ B) :
    Integrable (fun ω => Z ω * π.selectedTag (r ω) (x ω) (u ω) (a ω)) μ := by
  apply hZ.mul_bdd (π.measurable_selectedTag hπ hr hx hu ha).aestronglyMeasurable
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs] using π.selectedTag_abs_le (r ω) (x ω) (u ω) (a ω) hB hω

/-- Expected tag discrepancy is controlled by the two coupled outcome errors and
an unconditioned close-pair probability. No optimality assumption is used here. -/
lemma Policy.integral_selectedTag_difference_le [MeasurableSpace Seed']
    (π : Policy Seed n) (ρ : Policy Seed' n) (hπ : π.IsMeasurable) (hρ : ρ.IsMeasurable)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : Ω → Seed} {s : Ω → Seed'} {x u a : Ω → Fin n → ℝ}
    (hr : Measurable r) (hs : Measurable s) (hx : ∀ i, Measurable fun ω => x ω i)
    (hu : ∀ i, Measurable fun ω => u ω i) (ha : ∀ i, Measurable fun ω => a ω i)
    {B b η : ℝ} (hB : 0 ≤ B) (hb : 0 < b) (hη : 0 < η)
    (haB : ∀ᵐ ω ∂μ, ∀ i, |a ω i| ≤ B)
    (haz : ∀ᵐ ω ∂μ, ∀ i, x ω i < b → a ω i = 0)
    (hError : Integrable (fun ω =>
      |π.reward (r ω) Finset.univ (x ω) (u ω) - ρ.reward (s ω) Finset.univ (x ω) (u ω)| +
      |π.stoppingTime (r ω) Finset.univ (x ω) (u ω) - ρ.stoppingTime (s ω) Finset.univ (x ω) (u ω)|) μ) :
    (∫ ω, |π.selectedTag (r ω) (x ω) (u ω) (a ω) - ρ.selectedTag (s ω) (x ω) (u ω) (a ω)| ∂μ) ≤
      2 * B * (2 * (∫ ω,
        |π.reward (r ω) Finset.univ (x ω) (u ω) - ρ.reward (s ω) Finset.univ (x ω) (u ω)| +
        |π.stoppingTime (r ω) Finset.univ (x ω) (u ω) - ρ.stoppingTime (s ω) Finset.univ (x ω) (u ω)| ∂μ) / b +
        (∫ ω,
        |π.reward (r ω) Finset.univ (x ω) (u ω) - ρ.reward (s ω) Finset.univ (x ω) (u ω)| +
        |π.stoppingTime (r ω) Finset.univ (x ω) (u ω) - ρ.stoppingTime (s ω) Finset.univ (x ω) (u ω)| ∂μ) / η +
        μ.real {ω | closePositivePair (b / 2) η (x ω) (u ω)}) := by
  let Error : Ω → ℝ := fun ω =>
    |π.reward (r ω) Finset.univ (x ω) (u ω) - ρ.reward (s ω) Finset.univ (x ω) (u ω)| +
    |π.stoppingTime (r ω) Finset.univ (x ω) (u ω) - ρ.stoppingTime (s ω) Finset.univ (x ω) (u ω)|
  let Pair : Set Ω := {ω | closePositivePair (b / 2) η (x ω) (u ω)}
  let I : Ω → ℝ := fun ω => if ω ∈ Pair then 1 else 0
  have hPair : MeasurableSet Pair := measurableSet_closePositivePair hx hu _ _
  have hI : Integrable I μ := by
    apply Integrable.of_bound (Measurable.ite hPair measurable_const measurable_const).aestronglyMeasurable 1
    filter_upwards [] with ω
    dsimp [I]
    split_ifs <;> norm_num
  have hIeq : (∫ ω, I ω ∂μ) = μ.real Pair := by
    simpa only [I, Set.indicator_apply, Pi.one_apply] using (integral_indicator_one (μ := μ) hPair)
  have hTag := ((π.integrable_selectedTag hπ μ hr hx hu ha hB haB).sub
    (ρ.integrable_selectedTag hρ μ hs hx hu ha hB haB)).abs
  have hRHS : Integrable (fun ω => 2 * B * (2 * Error ω / b + Error ω / η + I ω)) μ :=
    (((hError.const_mul 2).div_const b).add (hError.div_const η) |>.add hI).const_mul (2 * B)
  have hpt : ∀ᵐ ω ∂μ,
      |π.selectedTag (r ω) (x ω) (u ω) (a ω) - ρ.selectedTag (s ω) (x ω) (u ω) (a ω)| ≤
        2 * B * (2 * Error ω / b + Error ω / η + I ω) := by
    filter_upwards [haB, haz] with ω hω hz
    apply (π.selectedTag_difference_le ρ (r ω) (s ω) (x ω) (u ω) (a ω) hB hb hη hω hz).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hB)
    have hR : |π.reward (r ω) Finset.univ (x ω) (u ω) - ρ.reward (s ω) Finset.univ (x ω) (u ω)| ≤ Error ω :=
      le_add_of_nonneg_right (abs_nonneg _)
    have hT : |π.stoppingTime (r ω) Finset.univ (x ω) (u ω) - ρ.stoppingTime (s ω) Finset.univ (x ω) (u ω)| ≤ Error ω :=
      le_add_of_nonneg_left (abs_nonneg _)
    have hRR : 2 * |π.reward (r ω) Finset.univ (x ω) (u ω) - ρ.reward (s ω) Finset.univ (x ω) (u ω)| / b ≤ 2 * Error ω / b :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 2)) hb.le
    have hTT := div_le_div_of_nonneg_right hT hη.le
    exact add_le_add (add_le_add hRR hTT) (le_refl (I ω))
  have h := integral_mono_ae hTag hRHS hpt
  have hE : Integrable Error μ := hError
  rw [integral_const_mul,
    integral_add (f := fun ω => 2 * Error ω / b + Error ω / η) (g := I)
      (((hE.const_mul 2).div_const b).add (hE.div_const η)) hI,
    integral_add (f := fun ω => 2 * Error ω / b) (g := fun ω => Error ω / η)
      ((hE.const_mul 2).div_const b) (hE.div_const η),
    integral_div, integral_div, integral_const_mul, hIeq] at h
  exact h

/-- A single candidate's uniform clock falls in an interval of length at most `2η`. -/
lemma Instance.uniformClock_close_le (z : ℝ) {η : ℝ} (_hη : 0 ≤ η) :
    Instance.uniformClock {t : ℝ | |t - z| ≤ η} ≤ ENNReal.ofReal (2 * η) := by
  have hs : {t : ℝ | |t - z| ≤ η} = Icc (z - η) (z + η) := by
    ext t
    simp only [mem_setOf_eq, abs_le, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hs]
  calc
    Instance.uniformClock (Icc (z - η) (z + η)) ≤ volume (Icc (z - η) (z + η)) :=
      Measure.restrict_le_self _
    _ = ENNReal.ofReal (2 * η) := by rw [Real.volume_Icc]; congr 1; ring

/-- Pair probability from actual independent offer marginals and uniform clocks.
The event is unconditioned, and may include clocks after either policy stopped. -/
lemma Instance.closePositivePair_single_probability (P : Instance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i j : Fin n) (hij : i ≠ j)
    (b : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    (P.worldLaw ν).real {ω : World n Seed |
      b < ω.1 i ∧ b < ω.1 j ∧ |ω.2.1 i - ω.2.1 j| ≤ η} ≤
      2 * η * (P.law i).real (Ioi b) * (P.law j).real (Ioi b) := by
  let μ := P.worldLaw ν
  let E : Set (World n Seed) := {ω | b < ω.1 i ∧ b < ω.1 j ∧ |ω.2.1 i - ω.2.1 j| ≤ η}
  let F : Set (World n Seed) := {ω | b < ω.1 i ∧ b < ω.1 j}
  have hx (k : Fin n) : Measurable (fun ω : World n Seed => ω.1 k) :=
    (measurable_pi_apply k).comp measurable_fst
  have hu (k : Fin n) : Measurable (fun ω : World n Seed => ω.2.1 k) :=
    (measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)
  have hF : MeasurableSet F := (measurableSet_lt measurable_const (hx i)).inter
    (measurableSet_lt measurable_const (hx j))
  have hE : MeasurableSet E := (measurableSet_lt measurable_const (hx i)).inter
    ((measurableSet_lt measurable_const (hx j)).inter
      (measurableSet_le (continuous_abs.measurable.comp ((hu i).sub (hu j))) measurable_const))
  have hp := P.replaceClock_measurePreserving ν i
  have hInner (ω : World n Seed) :
      Instance.uniformClock (Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E)) ≤
        F.indicator (fun _ => ENNReal.ofReal (2 * η)) ω := by
    by_cases h : ω ∈ F
    · rw [Set.indicator_of_mem h]
      have he : Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E) =
          {t : ℝ | |t - ω.2.1 j| ≤ η} := by
        ext t
        change (b < ω.1 i ∧ b < ω.1 j ∧
          |(Function.update ω.2.1 i t) i - (Function.update ω.2.1 i t) j| ≤ η) ↔ _
        simp only [Function.update_self, Function.update_of_ne hij.symm]
        exact and_iff_right h.1 |>.trans (and_iff_right h.2)
      rw [he]
      exact Instance.uniformClock_close_le _ hη
    · rw [Set.indicator_of_notMem h]
      have he : Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E) = ∅ := by
        ext t
        change (b < ω.1 i ∧ b < ω.1 j ∧ _) ↔ False
        constructor
        · exact fun ht => h ⟨ht.1, ht.2.1⟩
        · exact False.elim
      simp [he]
  have hFval : μ F = P.law i (Ioi b) * P.law j (Ioi b) := by
    have hv : MeasurePreserving (fun ω : World n Seed => ω.1) μ P.valuesLaw := measurePreserving_fst
    have hi := (measurePreserving_eval P.law i).measure_preimage (s := Ioi b) measurableSet_Ioi.nullMeasurableSet
    have hj := (measurePreserving_eval P.law j).measure_preimage (s := Ioi b) measurableSet_Ioi.nullMeasurableSet
    have hind := (P.values_independent.indepFun hij).measure_inter_preimage_eq_mul
      (Ioi b) (Ioi b) measurableSet_Ioi measurableSet_Ioi
    have hs : MeasurableSet {x : Fin n → ℝ | b < x i ∧ b < x j} :=
      (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
        (measurableSet_lt measurable_const (measurable_pi_apply j))
    change μ ((fun ω : World n Seed => ω.1) ⁻¹' {x : Fin n → ℝ | b < x i ∧ b < x j}) = _
    rw [hv.measure_preimage hs.nullMeasurableSet]
    exact hind.trans (congrArg₂ (· * ·) hi hj)
  have hbound : μ E ≤ ENNReal.ofReal (2 * η) * (P.law i (Ioi b) * P.law j (Ioi b)) := by
    calc
      μ E = (μ.prod Instance.uniformClock) ((Instance.replaceClock i) ⁻¹' E) :=
        (hp.measure_preimage hE.nullMeasurableSet).symm
      _ = ∫⁻ ω, Instance.uniformClock (Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E)) ∂μ :=
        Measure.prod_apply (hE.preimage hp.measurable)
      _ ≤ ∫⁻ ω, F.indicator (fun _ => ENNReal.ofReal (2 * η)) ω ∂μ := lintegral_mono hInner
      _ = ENNReal.ofReal (2 * η) * μ F := lintegral_indicator_const hF _
      _ = _ := by rw [hFval]
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))) hbound
  have h2 : 0 ≤ 2 * η := mul_nonneg (by norm_num) hη
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal h2] at hr
  simpa only [measureReal_def, mul_assoc] using hr

/-- The finite close-pair estimate has a universal constant and depends on the
expected positive tail count, not the number of offers. -/
theorem Instance.closePositivePair_probability (P : Instance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (b : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    (P.worldLaw ν).real {ω : World n Seed | closePositivePair b η ω.1 ω.2.1} ≤
      2 * η * (P.tailCount b) ^ 2 := by
  let E : Fin n → Fin n → Set (World n Seed) := fun i j =>
    {ω | i ≠ j ∧ b < ω.1 i ∧ b < ω.1 j ∧ |ω.2.1 i - ω.2.1 j| ≤ η}
  have heq : {ω : World n Seed | closePositivePair b η ω.1 ω.2.1} = ⋃ i, ⋃ j, E i j := by
    ext ω
    simp only [closePositivePair, E, mem_iUnion, mem_setOf_eq]
  rw [heq]
  have hsingle (i j : Fin n) : (P.worldLaw ν).real (E i j) ≤
      2 * η * (P.law i).real (Ioi b) * (P.law j).real (Ioi b) := by
    by_cases hij : i = j
    · subst j
      have he : E i i = ∅ := by ext ω; simp [E]
      rw [he, measureReal_empty]
      positivity
    · have he : E i j = {ω : World n Seed | b < ω.1 i ∧ b < ω.1 j ∧ |ω.2.1 i - ω.2.1 j| ≤ η} := by
        ext ω
        simp [E, hij]
      rw [he]
      exact P.closePositivePair_single_probability ν i j hij b hη
  calc
    _ ≤ ∑ i : Fin n, (P.worldLaw ν).real (⋃ j, E i j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (P.worldLaw ν).real (E i j) :=
      Finset.sum_le_sum (fun i _ => measureReal_iUnion_fintype_le _)
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        2 * η * (P.law i).real (Ioi b) * (P.law j).real (Ioi b) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hsingle i j))
    _ = 2 * η * (P.tailCount b) ^ 2 := by
      simp only [Instance.tailCount, measureReal_def, ← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring

/-- Explicit finite selected-occurrence estimate. Tags are common to both executions,
measurable, bounded, and zero below `b`. The competing policy remains completely
general. This numerical bound is independent of scalar optimality. -/
theorem RandomizedPolicy.selectedTag_stability_bound (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c B b η : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hB : 0 ≤ B) (hb : 0 < b) (hη : 0 < η)
    (a : π.World → Fin n → ℝ) (ha : ∀ i, Measurable fun ω => a ω i)
    (haB : ∀ᵐ ω ∂P.worldLaw π.seedLaw, ∀ i, |a ω i| ≤ B)
    (haz : ∀ᵐ ω ∂P.worldLaw π.seedLaw, ∀ i, ω.1 i < b → a ω i = 0) :
    (∫ ω : π.World,
      |π.rule.selectedTag ω.2.2 ω.1 ω.2.1 (a ω) -
        (P.canonicalRule w c).selectedTag () ω.1 ω.2.1 (a ω)| ∂P.worldLaw π.seedLaw) ≤
      2 * B * (2 * π.expectedOutcomeError P w c / b +
        π.expectedOutcomeError P w c / η + 2 * η * (P.tailCount (b / 2)) ^ 2) := by
  let ρ := P.canonicalRule w c
  have hρ : ρ.IsMeasurable := P.valueThreshold_policy_isMeasurable hP hw.le hc
  have hx (i : Fin n) : Measurable (fun ω : π.World => ω.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hu (i : Fin n) : Measurable (fun ω : π.World => ω.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have h := π.rule.integral_selectedTag_difference_le ρ π.measurable_rule hρ
    (P.worldLaw π.seedLaw) (measurable_snd.comp measurable_snd) measurable_const hx hu ha
    hB hb hη haB haz (π.integrable_coupledOutcomeError P hP hw hc)
  change (∫ ω : π.World,
      |π.rule.selectedTag ω.2.2 ω.1 ω.2.1 (a ω) - ρ.selectedTag () ω.1 ω.2.1 (a ω)| ∂P.worldLaw π.seedLaw) ≤
    2 * B * (2 * π.expectedOutcomeError P w c / b + π.expectedOutcomeError P w c / η +
      (P.worldLaw π.seedLaw).real {ω : π.World | closePositivePair (b / 2) η ω.1 ω.2.1}) at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (P.closePositivePair_probability π.seedLaw (b / 2) hη.le))
    (mul_nonneg (by norm_num) hB))

/-- The tag difference, and its product with any integrable analytical score, are
integrable. Independent auxiliary occurrence tags are included in this more general
common measurable assignment. -/
lemma RandomizedPolicy.selectedTag_difference_integrable (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c B : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (a : π.World → Fin n → ℝ) (ha : ∀ i, Measurable fun ω => a ω i)
    (haB : ∀ᵐ ω ∂P.worldLaw π.seedLaw, ∀ i, |a ω i| ≤ B) :
    Integrable (fun ω : π.World =>
      π.rule.selectedTag ω.2.2 ω.1 ω.2.1 (a ω) -
        (P.canonicalRule w c).selectedTag () ω.1 ω.2.1 (a ω)) (P.worldLaw π.seedLaw) ∧
    ∀ Z : π.World → ℝ, Integrable Z (P.worldLaw π.seedLaw) →
      Integrable (fun ω : π.World => Z ω *
        (π.rule.selectedTag ω.2.2 ω.1 ω.2.1 (a ω) -
          (P.canonicalRule w c).selectedTag () ω.1 ω.2.1 (a ω))) (P.worldLaw π.seedLaw) := by
  let ρ := P.canonicalRule w c
  have hρ : ρ.IsMeasurable := P.valueThreshold_policy_isMeasurable hP hw.le hc
  have hx (i : Fin n) : Measurable (fun ω : π.World => ω.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hu (i : Fin n) : Measurable (fun ω : π.World => ω.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hr : Measurable (fun ω : π.World => ω.2.2) := measurable_snd.comp measurable_snd
  refine ⟨(π.rule.integrable_selectedTag π.measurable_rule (P.worldLaw π.seedLaw) hr hx hu ha hB haB).sub
    (ρ.integrable_selectedTag hρ (P.worldLaw π.seedLaw) measurable_const hx hu ha hB haB), ?_⟩
  intro Z hZ
  have hp := π.rule.integrable_score_selectedTag π.measurable_rule (P.worldLaw π.seedLaw) hZ hr hx hu ha hB haB
  have hq := ρ.integrable_score_selectedTag hρ (P.worldLaw π.seedLaw) hZ (r := fun _ : π.World => ()) measurable_const hx hu ha hB haB
  apply (hp.sub hq).congr
  filter_upwards [] with ω
  change Z ω * π.rule.selectedTag ω.2.2 ω.1 ω.2.1 (a ω) -
    Z ω * ρ.selectedTag () ω.1 ω.2.1 (a ω) =
      Z ω * (π.rule.selectedTag ω.2.2 ω.1 ω.2.1 (a ω) - ρ.selectedTag () ω.1 ω.2.1 (a ω))
  ring

/-- Optimizing the separation parameter also treats zero outcome error, by letting
that separation tend to zero. -/
lemma selectedTag_error_optimize {B b L E T : ℝ} (hB : 0 ≤ B) (_hb : 0 < b)
    (hE : 0 ≤ E)
    (h : ∀ η : ℝ, 0 < η → T ≤ 2 * B * (2 * E / b + E / η + 2 * η * L ^ 2)) :
    T ≤ 2 * B * (2 * E / b + (1 + 2 * L ^ 2) * Real.sqrt E) := by
  by_cases hp : 0 < E
  · have hs : 0 < Real.sqrt E := Real.sqrt_pos.2 hp
    have hd : E / Real.sqrt E = Real.sqrt E :=
      (div_eq_iff hs.ne').mpr (by nlinarith [Real.sq_sqrt hE])
    have hh := h (Real.sqrt E) hs
    rw [hd] at hh
    convert hh using 1
    ring
  · have heq : E = 0 := le_antisymm (le_of_not_gt hp) hE
    rw [heq, Real.sqrt_zero]
    simp only [mul_zero, zero_div, add_zero]
    apply le_of_forall_pos_le_add
    intro ε hε
    let C := 4 * B * L ^ 2
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hD : 0 < C + 1 := by linarith
    let η := ε / (C + 1)
    have hη : 0 < η := div_pos hε hD
    have hh := h η hη
    rw [heq] at hh
    have hh' : T ≤ C * η := by
      convert hh using 1
      simp [C]
      ring
    have hfrac : C / (C + 1) ≤ 1 := (div_le_one hD).mpr (by linarith)
    have hεbound : C * η ≤ ε := by
      calc
        C * η = (C / (C + 1)) * ε := by dsimp [η]; ring
        _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hfrac hε.le
        _ = ε := one_mul _
    simpa only [zero_add] using hh'.trans hεbound

/-- The explicit tag-error profile is continuous at zero; no concavity is required. -/
noncomputable def selectedTagErrorBound (B b L E : ℝ) : ℝ :=
  2 * B * (2 * E / b + (1 + 2 * L ^ 2) * Real.sqrt E)

lemma selectedTagErrorBound_zero (B b L : ℝ) : selectedTagErrorBound B b L 0 = 0 := by
  simp [selectedTagErrorBound]

lemma continuous_selectedTagErrorBound (B b L : ℝ) : Continuous (selectedTagErrorBound B b L) := by
  unfold selectedTagErrorBound
  fun_prop

lemma selectedTagErrorBound_monotone {B b L : ℝ} (hB : 0 ≤ B) (hb : 0 < b) :
    Monotone (selectedTagErrorBound B b L) := by
  intro E F hEF
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hB)
  exact add_le_add (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hEF (by norm_num)) hb.le)
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEF) (by positivity))

lemma selectedTagErrorBound_nonnegative {B b L E : ℝ} (hB : 0 ≤ B) (hb : 0 < b) (hE : 0 ≤ E) :
    0 ≤ selectedTagErrorBound B b L E := by
  dsimp [selectedTagErrorBound]
  positivity

/-- Any outcome-error modulus tending to zero yields a tag-error modulus tending to
zero by composition with this explicit profile. -/
lemma selectedTagErrorBound_tendsto_zero {α : Type*} {l : Filter α} {f : α → ℝ}
    (hf : Filter.Tendsto f l (nhds 0)) (B b L : ℝ) :
    Filter.Tendsto (fun z => selectedTagErrorBound B b L (f z)) l (nhds 0) := by
  simpa only [selectedTagErrorBound_zero, Function.comp_def] using
    ((continuous_selectedTagErrorBound B b L).tendsto 0).comp hf

/-- Finite selected-occurrence stability in terms of the actual coupled outcome
error. The square-root modulus is uniform under a common positive tail-count bound. -/
theorem RandomizedPolicy.selectedTag_stability_sqrt (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c B b : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hB : 0 ≤ B) (hb : 0 < b)
    (a : π.World → Fin n → ℝ) (ha : ∀ i, Measurable fun ω => a ω i)
    (haB : ∀ᵐ ω ∂P.worldLaw π.seedLaw, ∀ i, |a ω i| ≤ B)
    (haz : ∀ᵐ ω ∂P.worldLaw π.seedLaw, ∀ i, ω.1 i < b → a ω i = 0) :
    (∫ ω : π.World,
      |π.rule.selectedTag ω.2.2 ω.1 ω.2.1 (a ω) -
        (P.canonicalRule w c).selectedTag () ω.1 ω.2.1 (a ω)| ∂P.worldLaw π.seedLaw) ≤
      2 * B * (2 * π.expectedOutcomeError P w c / b +
        (1 + 2 * (P.tailCount (b / 2)) ^ 2) * Real.sqrt (π.expectedOutcomeError P w c)) :=
  selectedTag_error_optimize hB hb (π.expectedOutcomeError_nonnegative P w c)
    (fun _ hη => π.selectedTag_stability_bound P hP hw hc hB hb hη a ha haB haz)

/-- A common outcome-error bound and a common positive tail bound give a common
selected-tag bound. All constants are independent of instance size. -/
theorem RandomizedPolicy.selectedTag_stability_of_outcome_bound (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c B b L W : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hB : 0 ≤ B) (hb : 0 < b)
    (hL : P.tailCount (b / 2) ≤ L) (hW : π.expectedOutcomeError P w c ≤ W)
    (a : π.World → Fin n → ℝ) (ha : ∀ i, Measurable fun ω => a ω i)
    (haB : ∀ᵐ ω ∂P.worldLaw π.seedLaw, ∀ i, |a ω i| ≤ B)
    (haz : ∀ᵐ ω ∂P.worldLaw π.seedLaw, ∀ i, ω.1 i < b → a ω i = 0) :
    (∫ ω : π.World,
      |π.rule.selectedTag ω.2.2 ω.1 ω.2.1 (a ω) -
        (P.canonicalRule w c).selectedTag () ω.1 ω.2.1 (a ω)| ∂P.worldLaw π.seedLaw) ≤
      2 * B * (2 * W / b + (1 + 2 * L ^ 2) * Real.sqrt W) := by
  apply (π.selectedTag_stability_sqrt P hP hw hc hB hb a ha haB haz).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hB)
  have hL0 := P.tailCount_nonnegative (b / 2)
  have hsq : (P.tailCount (b / 2)) ^ 2 ≤ L ^ 2 := by nlinarith
  have hcoef : 1 + 2 * (P.tailCount (b / 2)) ^ 2 ≤ 1 + 2 * L ^ 2 := by linarith
  exact add_le_add
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by norm_num)) hb.le)
    (mul_le_mul hcoef (Real.sqrt_le_sqrt hW) (Real.sqrt_nonneg _) (by positivity))

/-- Zero outcome error identifies every common bounded positive-level selected tag
almost surely. The occurrence itself is controlled by the independent close-pair
estimate, rather than inferred from equality of reward values alone. -/
theorem RandomizedPolicy.selectedTag_eq_ae_of_zero_outcomeError (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c B b : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hB : 0 ≤ B) (hb : 0 < b)
    (hE : π.expectedOutcomeError P w c = 0)
    (a : π.World → Fin n → ℝ) (ha : ∀ i, Measurable fun ω => a ω i)
    (haB : ∀ᵐ ω ∂P.worldLaw π.seedLaw, ∀ i, |a ω i| ≤ B)
    (haz : ∀ᵐ ω ∂P.worldLaw π.seedLaw, ∀ i, ω.1 i < b → a ω i = 0) :
    ∀ᵐ ω : π.World ∂P.worldLaw π.seedLaw,
      π.rule.selectedTag ω.2.2 ω.1 ω.2.1 (a ω) =
        (P.canonicalRule w c).selectedTag () ω.1 ω.2.1 (a ω) := by
  have h := π.selectedTag_stability_sqrt P hP hw hc hB hb a ha haB haz
  rw [hE, Real.sqrt_zero] at h
  simp only [mul_zero, zero_div, add_zero] at h
  have hI := (π.selectedTag_difference_integrable P hP hw hc hB a ha haB).1.abs
  have heq := (integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _) hI).1
    (le_antisymm h (integral_nonneg (fun _ => abs_nonneg _)))
  filter_upwards [heq] with ω hω
  exact sub_eq_zero.mp (abs_eq_zero.mp hω)

end ProphetSecretary.Model
