import ProphetSecretary.Limiting.CountableExcessOverlap
import ProphetSecretary.Model.Independence

/-!
# A single individual carries all excess under prophet equality

Equality between total expected cap excess and actual maximum excess eliminates
Poisson upper tails and all simultaneous positive individual excesses. The
latter uses the actual independent individual product law. Positive total
excess therefore belongs to exactly one individual. This is the concentration
step in `lem:boundary-slack`.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal
namespace ProphetSecretary.Limiting.CountableInstance

lemma tailValue_pos_of_gt_cap (K : ℝ≥0) {x : ℝ} (hx : (K : ℝ) < x) : 0 < Model.tailValue K x :=
  (sub_pos.mpr hx).trans_le (le_max_left _ _)

lemma integral_tailValue_zero_of_tail_null (μ : Measure ℝ) (K : ℝ≥0) (hNull : μ (Ioi (K : ℝ))=0) :
    (∫ x, Model.tailValue K x ∂μ)=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hNull] with x hx
  have hLe : x ≤ (K : ℝ) := not_lt.mp hx
  exact max_eq_right (sub_nonpos.mpr hLe)

lemma individualCapExcess_zero_iff_tail_zero (B : CountableInstance) (K : ℝ≥0) (i : ℕ) :
    B.individualCapExcess K i=0 ↔ (B.individuals i : Measure ℝ) (Ioi (K : ℝ))=0 := by
  constructor
  · intro hZero
    have hAE := (integral_eq_zero_iff_of_nonneg (Model.tailValue_nonnegative K)
      (B.individualCapExcess_integrable K i)).mp hZero
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hAE] with x hx hAbove
    exact (ne_of_gt (tailValue_pos_of_gt_cap K hAbove)) hx
  · exact integral_tailValue_zero_of_tail_null _ K

lemma poissonCapExcess_zero_of_tail_zero (B : CountableInstance) (K : ℝ≥0)
    (hNull : B.intensity (Ioi (K : ℝ))=0) : B.poissonCapExcess K=0 :=
  integral_tailValue_zero_of_tail_null _ K hNull

lemma individualCapOverlap_integral_positive (B : CountableInstance) (K : ℝ≥0) (i j : ℕ) (hij : i ≠ j)
    (hi : (B.individuals i : Measure ℝ) (Ioi (K : ℝ)) ≠ 0)
    (hj : (B.individuals j : Measure ℝ) (Ioi (K : ℝ)) ≠ 0) :
    0 < ∫ v, individualCapOverlap K i j v ∂B.valueLaw := by
  have hMP : MeasurePreserving (Prod.snd : ValueWorld → (ℕ → ℝ)) B.valueLaw B.individualValuesLaw :=
    measurePreserving_snd
  have hInd : IndepFun (fun v : ValueWorld => v.2 i) (fun v => v.2 j) B.valueLaw :=
    Model.indepFun_pullback hMP (measurable_pi_apply i) (measurable_pi_apply j)
      (B.individualValues_independent.indepFun hij)
  have hMargI : B.valueLaw {v : ValueWorld | (K : ℝ) < v.2 i}=(B.individuals i : Measure ℝ) (Ioi (K : ℝ)) :=
    (B.individualCapExcess_valueWorld_measurePreserving i).measure_preimage measurableSet_Ioi.nullMeasurableSet
  have hMargJ : B.valueLaw {v : ValueWorld | (K : ℝ) < v.2 j}=(B.individuals j : Measure ℝ) (Ioi (K : ℝ)) :=
    (B.individualCapExcess_valueWorld_measurePreserving j).measure_preimage measurableSet_Ioi.nullMeasurableSet
  have hPair := hInd.measure_inter_preimage_eq_mul (Ioi (K : ℝ)) (Ioi (K : ℝ)) measurableSet_Ioi measurableSet_Ioi
  change B.valueLaw {v : ValueWorld | (K : ℝ) < v.2 i ∧ (K : ℝ) < v.2 j}=
    B.valueLaw {v : ValueWorld | (K : ℝ) < v.2 i}*B.valueLaw {v : ValueWorld | (K : ℝ) < v.2 j} at hPair
  rw [hMargI,hMargJ] at hPair
  have hPositive : 0 < B.valueLaw {v : ValueWorld | (K : ℝ) < v.2 i ∧ (K : ℝ) < v.2 j} := by
    rw [hPair]
    exact ENNReal.mul_pos_iff.mpr ⟨pos_iff_ne_zero.mpr hi,pos_iff_ne_zero.mpr hj⟩
  apply (integral_pos_iff_support_of_nonneg (individualCapOverlap_nonnegative K i j)
    (B.integrable_individualCapOverlap K i j)).mpr
  apply hPositive.trans_le
  apply measure_mono
  intro v hv
  exact ne_of_gt (lt_min (tailValue_pos_of_gt_cap K hv.1) (tailValue_pos_of_gt_cap K hv.2))

/-- The threshold is strictly above reserve; neither positive expected maximum
nor a bound on total first moments near reserve is imposed. -/
theorem capExcess_concentrates_on_one_individual (B : CountableInstance) (K : ℝ≥0)
    (hK : (B.terminal : ℝ) < K) (hPos : 0 < B.totalCapExcess K)
    (hEq : B.totalCapExcess K=∫ v, Model.tailValue K (B.maximum v) ∂B.valueLaw) :
    B.intensity (Ioi (K : ℝ))=0 ∧ ∃ j : ℕ,
      (∀ i, i ≠ j → (B.individuals i : Measure ℝ) (Ioi (K : ℝ))=0) ∧
      B.individualCapExcess K j=B.totalCapExcess K ∧ 0 < B.individualCapExcess K j := by
  have hμ := B.intensity_tail_zero_of_prophet_excess_equality K hK hEq
  have hμE := B.poissonCapExcess_zero_of_tail_zero K hμ
  have hExists : ∃ j, 0 < B.individualCapExcess K j := by
    by_contra h
    push Not at h
    have hAll (i : ℕ) : B.individualCapExcess K i=0 :=
      le_antisymm (h i) (B.individualCapExcess_nonnegative K i)
    have hTotal : B.totalCapExcess K=0 := by simp only [totalCapExcess,hAll,tsum_zero,hμE,add_zero]
    exact (ne_of_gt hPos) hTotal
  obtain ⟨j,hj⟩ := hExists
  have hTailJ : (B.individuals j : Measure ℝ) (Ioi (K : ℝ)) ≠ 0 :=
    fun hNull => (ne_of_gt hj) ((B.individualCapExcess_zero_iff_tail_zero K j).mpr hNull)
  have hOthers (i : ℕ) (hij : i ≠ j) : (B.individuals i : Measure ℝ) (Ioi (K : ℝ))=0 := by
    by_contra hi
    have hPositive := B.individualCapOverlap_integral_positive K i j hij hi hTailJ
    exact (ne_of_gt hPositive) (B.individualCapOverlap_integral_zero_of_prophet_equality K hK hEq i j hij)
  refine ⟨hμ,j,hOthers,?_,hj⟩
  have hSum : (∑' i, B.individualCapExcess K i)=B.individualCapExcess K j :=
    tsum_eq_single j (fun i hij => (B.individualCapExcess_zero_iff_tail_zero K i).mpr (hOthers i hij))
  rw [totalCapExcess,hSum,hμE,add_zero]

/-- Zero-reserve formulation used by the boundary-slack argument. -/
theorem single_individual_capExcess_of_prophet_equality (B : CountableInstance) (hZero : B.terminal=0)
    (K : ℝ≥0) (hK : 0 < K) (hPos : 0 < B.totalCapExcess K)
    (hEq : B.totalCapExcess K=∫ v, Model.tailValue K (B.maximum v) ∂B.valueLaw) :
    B.intensity (Ioi (K : ℝ))=0 ∧ ∃ j : ℕ,
      (∀ i, i ≠ j → (B.individuals i : Measure ℝ) (Ioi (K : ℝ))=0) ∧
      B.individualCapExcess K j=B.totalCapExcess K ∧ 0 < B.individualCapExcess K j := by
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  exact B.capExcess_concentrates_on_one_individual K (by simpa only [hZero,NNReal.coe_zero] using hKR) hPos hEq

end ProphetSecretary.Limiting.CountableInstance
