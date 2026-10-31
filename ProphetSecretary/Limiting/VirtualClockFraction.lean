import ProphetSecretary.Limiting.HazardFluctuation

/-!
# Fraction of unseen virtual identities

For q independent uniform clocks, the unseen fraction has mean absolute error
at most 1/√q from the remaining horizon. Clock equalities have zero probability,
so the strict-tail and actual unseen (weak-tail) counts agree almost surely.
The estimate concerns complete clock vectors analytically, not policy inputs.
-/
open MeasureTheory Set Filter
open scoped Topology Classical BigOperators
namespace ProphetSecretary.Limiting
variable {q : ℕ}

noncomputable def virtualSurvivalFraction (t : ℝ) (v : Fin q → ℝ) : ℝ :=
  (∑ j, if t < v j then (1 : ℝ) else 0)/(q : ℝ)

lemma virtualSurvivalFraction_centered {t : ℝ} (hq : 0 < q) (v : Fin q → ℝ) :
    virtualSurvivalFraction t v-(1-t) =
      -(∑ j : Fin q, ProphetSecretary.Probability.centeredIndicator (Iic t) t (v j))/(q : ℝ) := by
  have hs : (∑ j : Fin q, if t < v j then (1 : ℝ) else 0) =
      (q : ℝ)-(∑ j : Fin q, if v j ≤ t then (1 : ℝ) else 0) := by
    rw [← show (∑ _j : Fin q, (1 : ℝ)) = (q : ℝ) by simp,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : v j ≤ t <;> simp [hj,not_lt.mpr,lt_of_not_ge]
  unfold virtualSurvivalFraction ProphetSecretary.Probability.centeredIndicator
  simp only [mem_Iic,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [hs]
  have hqR : (q : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hq)
  field_simp
  ring

/-- Uniform in physical time and the number of clocks. -/
theorem virtualSurvivalFraction_absoluteMean_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hq : 0 < q) :
    (∫ v : Fin q → ℝ, |virtualSurvivalFraction t v-(1-t)| ∂Model.Instance.clocksLaw q) ≤
      1/Real.sqrt (q : ℝ) := by
  have hp : Model.Instance.uniformClock.real (Iic t) = t := by
    rw [Measure.real,uniformClock_Iic ht,ENNReal.toReal_ofReal ht.1]
  have hMean := ProphetSecretary.Probability.weighted_centeredIndicator_absoluteMean
    Model.Instance.uniformClock (A := Iic t) measurableSet_Iic (fun _ : Fin q => (1 : ℝ))
  simp only [hp,one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hMean
  have hsq : t*(1-t)*(q : ℝ) ≤ (q : ℝ) := by
    have hbase : t*(1-t) ≤ 1 := by nlinarith [sq_nonneg t]
    exact (mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg q)).trans_eq (one_mul _)
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  calc
    _ = (∫ v : Fin q → ℝ, |∑ j : Fin q, ProphetSecretary.Probability.centeredIndicator (Iic t) t (v j)|
        ∂Model.Instance.clocksLaw q)/(q : ℝ) := by
      simp_rw [virtualSurvivalFraction_centered hq,abs_div,abs_neg,abs_of_pos hqR]
      exact integral_div _ _
    _ ≤ Real.sqrt (t*(1-t)*(q : ℝ))/(q : ℝ) := div_le_div_of_nonneg_right hMean hqR.le
    _ ≤ Real.sqrt (q : ℝ)/(q : ℝ) := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hsq) hqR.le
    _ = _ := Real.sqrt_div_self'

lemma virtualClockFraction_error_tendsto_zero :
    Tendsto (fun q : ℕ => 1/Real.sqrt (q : ℝ)) atTop (𝓝 (0 : ℝ)) :=
  tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

noncomputable def virtualUnseenCount (t : ℝ) (v : Fin q → ℝ) : ℕ :=
  (Finset.univ.filter fun j => t ≤ v j).card

lemma virtualUnseenCount_le (t : ℝ) (v : Fin q → ℝ) : virtualUnseenCount t v ≤ q := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

lemma virtualUnseenCount_fraction_ae (t : ℝ) :
    (fun v : Fin q → ℝ => (virtualUnseenCount t v : ℝ)/(q : ℝ)) =ᵐ[Model.Instance.clocksLaw q]
      virtualSurvivalFraction t := by
  have hNe : ∀ᵐ v ∂Model.Instance.clocksLaw q, ∀ j : Fin q, v j ≠ t :=
    ae_all_iff.mpr (fun j => (measurePreserving_eval (fun _ : Fin q => Model.Instance.uniformClock) j).quasiMeasurePreserving.ae
      (Model.Instance.uniformClock.ae_ne t))
  filter_upwards [hNe] with v hv
  unfold virtualSurvivalFraction virtualUnseenCount
  congr 1
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro j _
  have he : t ≤ v j ↔ t < v j := le_iff_lt_or_eq.trans (or_iff_left (hv j).symm)
  simp only [he]

lemma measurable_virtualUnseenFraction :
    Measurable (fun z : ℝ × (Fin q → ℝ) => (virtualUnseenCount z.1 z.2 : ℝ)/(q : ℝ)) := by
  unfold virtualUnseenCount
  simp_rw [← Finset.sum_boole]
  apply Measurable.div_const
  apply Finset.measurable_fun_sum
  intro j _
  exact Measurable.ite (measurableSet_le measurable_fst ((measurable_pi_apply j).comp measurable_snd))
    measurable_const measurable_const

lemma integrable_virtualSurvivalFraction_error (t : ℝ) :
    Integrable (fun v : Fin q → ℝ => |virtualSurvivalFraction t v-(1-t)|)
      (Model.Instance.clocksLaw q) := by
  have hEach (j : Fin q) : Integrable (fun v : Fin q → ℝ => if t < v j then (1 : ℝ) else 0)
      (Model.Instance.clocksLaw q) := by
    have hm : Measurable (fun v : Fin q → ℝ => if t < v j then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply j)) measurable_const measurable_const
    apply Integrable.of_bound (μ := Model.Instance.clocksLaw q) hm.aestronglyMeasurable (1 : ℝ)
    exact Eventually.of_forall fun v => by split_ifs <;> norm_num
  have hSum : Integrable (fun v : Fin q → ℝ => ∑ j, if t < v j then (1 : ℝ) else 0)
      (Model.Instance.clocksLaw q) := integrable_finsetSum Finset.univ fun j _ => hEach j
  exact ((hSum.div_const (q : ℝ)).sub (integrable_const (1-t))).abs

lemma integrable_virtualUnseenFraction_error (t : ℝ) :
    Integrable (fun v : Fin q → ℝ => |(virtualUnseenCount t v : ℝ)/(q : ℝ)-(1-t)|)
      (Model.Instance.clocksLaw q) := by
  have he : (fun v : Fin q → ℝ => |(virtualUnseenCount t v : ℝ)/(q : ℝ)-(1-t)|) =ᵐ[Model.Instance.clocksLaw q]
      (fun v => |virtualSurvivalFraction t v-(1-t)|) :=
    (virtualUnseenCount_fraction_ae (q := q) t).mono fun _ h => congrArg (fun x : ℝ => |x-(1-t)|) h
  exact (integrable_virtualSurvivalFraction_error (q := q) t).congr he.symm

/-- The bound applies to the actual unseen count, including zero identity
observations. Strict-tail replacement is justified almost surely above. -/
theorem virtualUnseenFraction_absoluteMean_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hq : 0 < q) :
    (∫ v : Fin q → ℝ, |(virtualUnseenCount t v : ℝ)/(q : ℝ)-(1-t)| ∂Model.Instance.clocksLaw q) ≤
      1/Real.sqrt (q : ℝ) := by
  calc
    _ = ∫ v : Fin q → ℝ, |virtualSurvivalFraction t v-(1-t)| ∂Model.Instance.clocksLaw q := by
      apply integral_congr_ae
      exact (virtualUnseenCount_fraction_ae (q := q) t).mono fun _ h => congrArg (fun x : ℝ => |x-(1-t)|) h
    _ ≤ _ := virtualSurvivalFraction_absoluteMean_le ht hq

end ProphetSecretary.Limiting
