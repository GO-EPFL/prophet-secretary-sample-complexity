import ProphetSecretary.Limiting.CountableAcceptedPointMeasure

/-!
# First-point reward for countable sums of finite components

The accepted set may contain infinitely many analytical acceptances after its
first point. Its total measure need not be finite. Componentwise finite
parameter integrals still prove measurability of the actual first reward.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting.FirstPoint

noncomputable def markIntegralAt (μ : Measure Point) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, if p.1 = t then ENNReal.ofReal p.2 else 0 ∂μ

noncomputable def rawReward (a : ℝ) (μ : Measure Point) : ℝ :=
  if μ univ = 0 then a else (markIntegralAt μ (time μ)).toReal

lemma reward_eq_rawReward (a : ℝ) (μ : FiniteMeasure Point) : reward a μ = rawReward a (μ : Measure Point) := rfl

lemma rawReward_of_firstSlice (a : ℝ) (μ : Measure Point) {x : ℝ} (hx : 0 ≤ x)
    (hne : μ univ ≠ 0)
    (hslice : μ.restrict {p : Point | p.1 = time μ} = Measure.dirac (time μ,x)) : rawReward a μ = x := by
  have hS : MeasurableSet {p : Point | p.1 = time μ} := measurableSet_eq_fun measurable_fst measurable_const
  have he : (fun p : Point => if p.1 = time μ then ENNReal.ofReal p.2 else 0) =
      {p : Point | p.1 = time μ}.indicator (fun p => ENNReal.ofReal p.2) := by funext p; rfl
  rw [rawReward,if_neg hne,markIntegralAt,he,lintegral_indicator hS,hslice,lintegral_dirac]
  exact ENNReal.toReal_ofReal hx

lemma measurable_markIntegralAt_finite :
    Measurable (fun q : FiniteMeasure Point × ℝ => markIntegralAt (q.1 : Measure Point) q.2) := by
  unfold markIntegralAt
  apply ProphetSecretary.Probability.measurable_lintegral_finiteFamily
    (μ := fun q : FiniteMeasure Point × ℝ => q.1)
    (f := fun q : (FiniteMeasure Point × ℝ) × Point => if q.2.1 = q.1.2 then ENNReal.ofReal q.2.2 else 0)
    measurable_fst
  exact Measurable.ite (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_fst)) (measurable_snd.comp measurable_snd).ennreal_ofReal measurable_const

lemma measurable_rawReward_sumFinite {Ω : Type*} [MeasurableSpace Ω]
    (a : ℝ) {μ : ℕ → Ω → FiniteMeasure Point} (hμ : ∀ i, Measurable (μ i)) :
    Measurable (fun ω => rawReward a (Measure.sum (fun i => (μ i ω : Measure Point)))) := by
  let M : Ω → Measure Point := fun ω => Measure.sum (fun i => (μ i ω : Measure Point))
  have hM : Measurable M := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have he : (fun ω => M ω S) = fun ω => ∑' i, (μ i ω : Measure Point) S := by
      funext ω
      exact Measure.sum_apply _ hS
    rw [he]
    exact Measurable.tsum (fun i => (Measure.measurable_coe hS).comp (measurable_subtype_coe.comp (hμ i)))
  have ht : Measurable (fun ω => time (M ω)) := measurable_time.comp hM
  have hnum : Measurable (fun ω => ∑' i, markIntegralAt (μ i ω : Measure Point) (time (M ω))) :=
    Measurable.tsum (fun i => measurable_markIntegralAt_finite.comp ((hμ i).prodMk ht))
  have heNum (ω : Ω) : markIntegralAt (M ω) (time (M ω)) =
      ∑' i, markIntegralAt (μ i ω : Measure Point) (time (M ω)) := by
    change (∫⁻ p, if p.1 = time (M ω) then ENNReal.ofReal p.2 else 0
      ∂Measure.sum (fun i => (μ i ω : Measure Point))) = _
    rw [lintegral_sum_measure]
    rfl
  have he : (fun ω => rawReward a (M ω)) = fun ω => if M ω univ = 0 then a else
      (∑' i, markIntegralAt (μ i ω : Measure Point) (time (M ω))).toReal := by
    funext ω
    rw [rawReward,heNum]
  change Measurable (fun ω => rawReward a (M ω))
  rw [he]
  exact Measurable.ite (measurableSet_eq_fun ((Measure.measurable_coe MeasurableSet.univ).comp hM)
    measurable_const) measurable_const hnum.ennreal_toReal

end ProphetSecretary.Limiting.FirstPoint

namespace ProphetSecretary.Limiting.FirstAcceptance

variable {Ω : Type*}

lemma pointMeasure_rawReward_eq (a : ℝ) {A : Ω → ℕ → Prop} {u x : Ω → ℕ → ℝ} {ω : Ω}
    (hfirst : HasFirstIfAccepted A u ω) (hu : ∀ i, A ω i → u ω i ∈ Icc (0 : ℝ) 1)
    (hx : ∀ i, A ω i → 0 ≤ x ω i) (hinj : Set.InjOn (u ω) {i | A ω i}) :
    FirstPoint.rawReward a (pointMeasure A u x ω) = reward a A u x ω := by
  by_cases he : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := he
    rw [reward_of_earliest a hi]
    have ht : FirstPoint.time (pointMeasure A u x ω) = u ω i := by
      rw [pointMeasure_time_eq hfirst hu,stoppingTime_of_earliest hi]
    have hne : pointMeasure A u x ω univ ≠ 0 := by
      have hle := Measure.le_iff.mp
        (Measure.le_sum (fun j => if A ω j then Measure.dirac (u ω j,x ω j) else 0) i)
        univ MeasurableSet.univ
      simp only [if_pos hi.1,measure_univ] at hle
      exact ne_of_gt (zero_lt_one.trans_le hle)
    apply FirstPoint.rawReward_of_firstSlice a _ (hx i hi.1) hne
    rw [ht]
    exact pointMeasure_firstSlice hi.1 hinj
  · have hno := (no_first_iff_no_accepted hfirst).mp he
    rw [reward,(selectedCode_eq_zero_iff _ _ _).mpr he,if_pos rfl,pointMeasure_eq_zero hno]
    simp [FirstPoint.rawReward]

end ProphetSecretary.Limiting.FirstAcceptance
