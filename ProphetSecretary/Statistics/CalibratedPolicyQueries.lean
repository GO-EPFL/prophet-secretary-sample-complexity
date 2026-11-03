import ProphetSecretary.Statistics.CalibratedPolicyFamily
import ProphetSecretary.Statistics.EmpiricalPlannerInstance
import ProphetSecretary.Statistics.PlannerRoundedComparisons

/-!
# Confidence of the queries on a numerical policy trajectory

The complete offer and clock vector fixes every potential query state and
its seed coordinate. This vector is used only for analysis. The actual
callback receives its current observation and strict past.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} [NeZero m] {PSeed : Type*} [MeasurableSpace PSeed]

lemma continuationIdentities_eq_active (y : Reservoir n m) (H : History n) (i : Fin n) :
    continuationIdentities y H i = plannerActive (k := fun _ => m) y ((unseen H).erase i) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  ext j
  simp only [continuationIdentities, plannerActive, Finset.mem_filter]
  apply and_congr_right
  intro _
  simp only [plannerPositiveProbability, empiricalPositiveProbability, lt_div_iff₀ hm, zero_mul,
    Nat.cast_pos, Finset.card_pos]
  simp [positiveObservations, Finset.Nonempty]

noncomputable def policyQueryError (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (i : Fin n) (j : Fin (J+1))
    (ω : World n (PolicyQueryArray n J PSeed)) : ℝ :=
  |familyQuery zlo zhi estimate (y,ω.2.2) (ω.2.1 i) i
      (history Finset.univ ω.1 ω.2.1 (ω.2.1 i)) j.val -
    (totalEmpiricalInstance y).continuationAtArrival 1 (familyCoefficient zlo zhi J j.val) ω.1 ω.2.1 i|

/-- A fixed potential query has the prescribed confidence on the actual product world. -/
theorem policyQueryError_probability_le (P : Instance n) (ν : Measure PSeed) [IsProbabilityMeasure ν]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (hm : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
    (y : Reservoir n m) (hy : ∀ i l, 0 ≤ y i l) (i : Fin n) (j : Fin (J+1))
    {h δ : ℝ} (hz : familyCoefficient zlo zhi J j.val ∈ Icc (0 : ℝ) 4)
    (hconf : ∀ (A : Finset (Fin n)) (u z : ℝ), u ∈ Icc (0 : ℝ) 1 → z ∈ Icc (0 : ℝ) 4 →
      ν.real {s | h < |estimate y A u z s - (totalEmpiricalInstance y).continuationValue A u 1 z|} ≤ δ) :
    (P.worldLaw (policyQueryArrayLaw (n := n) (J := J) ν)).real
      {ω | h < policyQueryError zlo zhi estimate y i j ω} ≤ δ := by
  let Q := totalEmpiricalInstance y
  let z := familyCoefficient zlo zhi J j.val
  let Ξ := PolicyQueryArray n J PSeed
  let Ω := World n Ξ
  let νa : Measure Ξ := policyQueryArrayLaw ν
  let γ := P.valuesLaw.prod (Instance.clocksLaw n)
  let E : Set Ω := {ω | h < policyQueryError zlo zhi estimate y i j ω}
  have hv (a : Fin n) : Measurable (fun ω : Ω => ω.1 a) := (measurable_pi_apply a).comp measurable_fst
  have hu (a : Fin n) : Measurable (fun ω : Ω => ω.2.1 a) :=
    (measurable_pi_apply a).comp (measurable_fst.comp measurable_snd)
  have hh := measurable_history Finset.univ hv hu (hu i)
  have he := measurable_familyQuery (J := J) zlo zhi estimate hm
    (y := fun _ : Ω => y) (r := fun ω : Ω => ω.2.2)
    (measurable_const (a := y)) (measurable_snd.comp measurable_snd)
    (hu i) (measurable_const (a := i)) hh j.val
  have hc := Q.measurable_continuationAtArrival (totalEmpiricalInstance_integrable y)
    (by norm_num : (0 : ℝ) < 1) hz.1 hv hu i
  have hE : MeasurableSet E := measurableSet_lt measurable_const (continuous_abs.measurable.comp (he.sub hc))
  let e : ((Fin n → ℝ) × (Fin n → ℝ)) × Ξ ≃ᵐ Ω := MeasurableEquiv.prodAssoc
  have hp : MeasurePreserving e (γ.prod νa) (P.worldLaw νa) :=
    measurePreserving_prodAssoc P.valuesLaw (Instance.clocksLaw n) νa
  change (P.worldLaw νa).real E ≤ δ
  rw [← hp.map_eq, map_measureReal_apply hp.measurable hE]
  apply product_event_probability_le γ νa _ (hE.preimage hp.measurable) δ
  have hclock : MeasurePreserving (Prod.snd : ((Fin n → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
      γ (Instance.clocksLaw n) := measurePreserving_snd
  filter_upwards [hclock.quasiMeasurePreserving.ae (Instance.clocks_mem_unitInterval (n := n))] with v hvu
  let H := history Finset.univ v.1 v.2 (v.2 i)
  let A := continuationIdentities y H i
  let u := unitRemaining (v.2 i)
  let idx := (currentRankFromClock i H, j)
  have hrem : 0 ≤ 1-v.2 i := sub_nonneg.mpr (hvu i).2
  letI : ∀ _ : Fin n, NeZero m := fun _ => inferInstance
  have hQeq : Q = empiricalPlannerInstance (k := fun _ => m) y hy := by
    exact (totalEmpiricalInstance_eq y hy).trans (Instance.eq_of_law_eq rfl)
  have hval : Q.continuationAtArrival 1 z v.1 v.2 i = Q.continuationValue A u 1 z := by
    change Q.continuationValue ((unseen H).erase i) (max 0 (1-v.2 i)) 1 z = _
    rw [max_eq_right hrem, show u = 1-v.2 i from unitRemaining_eq (hvu i), hQeq]
    dsimp [A]
    rw [continuationIdentities_eq_active]
    exact empiricalPlannerInstance_active_value (k := fun _ => m) y hy ((unseen H).erase i) hrem hz.1
  let E0 : Set PSeed := {s | h < |estimate y A u z s-Q.continuationValue A u 1 z|}
  have hEval : Measurable (estimate y A u z) := hm.comp
    (measurable_const.prodMk (measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))))
  have hE0 : MeasurableSet E0 := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (hEval.sub_const _))
  have hidx : coefficientIndex J j.val = j := Fin.ext (min_eq_left (Nat.le_of_lt_succ j.isLt))
  have hsec : Prod.mk v ⁻¹' (e ⁻¹' E) = (fun r : Ξ => r idx) ⁻¹' E0 := by
    ext r
    change (h < |familyQuery zlo zhi estimate (y,r) (v.2 i) i H j.val -
      Q.continuationAtArrival 1 z v.1 v.2 i|) ↔ h < |estimate y A u z (r idx)-Q.continuationValue A u 1 z|
    simp only [hval, familyQuery, hidx, A, u, z, idx]
  rw [hsec]
  have hproj : MeasurePreserving (fun r : Ξ => r idx) νa ν :=
    measurePreserving_eval (fun _ : Fin n × Fin (J+1) => ν) idx
  rw [← map_measureReal_apply hproj.measurable hE0, hproj.map_eq]
  exact hconf A u z (unitRemaining_range _) hz

/-- Union bound over the actual finite family of potential continuation calls. -/
theorem policyQueryFailure_probability_le (P : Instance n) (ν : Measure PSeed) [IsProbabilityMeasure ν]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (hm : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
    (y : Reservoir n m) (hy : ∀ i l, 0 ≤ y i l) {h δ : ℝ}
    (hz : ∀ j : Fin (J+1), familyCoefficient zlo zhi J j.val ∈ Icc (0 : ℝ) 4)
    (hconf : ∀ (A : Finset (Fin n)) (u z : ℝ), u ∈ Icc (0 : ℝ) 1 → z ∈ Icc (0 : ℝ) 4 →
      ν.real {s | h < |estimate y A u z s - (totalEmpiricalInstance y).continuationValue A u 1 z|} ≤ δ) :
    (P.worldLaw (policyQueryArrayLaw (n := n) (J := J) ν)).real
      {ω | ∃ (i : Fin n) (j : Fin (J+1)), h < policyQueryError zlo zhi estimate y i j ω} ≤
      (n : ℝ)*(J+1)*δ := by
  let μ := P.worldLaw (policyQueryArrayLaw (n := n) (J := J) ν)
  let E : Fin n × Fin (J+1) → Set (World n (PolicyQueryArray n J PSeed)) :=
    fun a => {ω | h < policyQueryError zlo zhi estimate y a.1 a.2 ω}
  have he : {ω | ∃ (i : Fin n) (j : Fin (J+1)), h < policyQueryError zlo zhi estimate y i j ω} =
      ⋃ a, E a := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E, Prod.exists]
  rw [he]
  calc
    _ ≤ ∑ a, μ.real (E a) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _a : Fin n × Fin (J+1), δ := Finset.sum_le_sum fun a _ =>
      policyQueryError_probability_le P ν zlo zhi estimate hm y hy a.1 a.2 (hz a.2) hconf
    _ = _ := by simp [Fintype.card_prod, Nat.cast_add, Nat.cast_mul]

/-- Prefix maxima retain the uniform accuracy of the underlying queried values. -/
theorem familyThresholdError_probability_le (P : Instance n) (ν : Measure PSeed) [IsProbabilityMeasure ν]
    {zlo zhi : ℝ} (hord : zlo ≤ zhi) (estimate : ContinuationEstimator n m PSeed)
    (hm : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
    (y : Reservoir n m) (hy : ∀ i l, 0 ≤ y i l) {h δ : ℝ} (hh : 0 ≤ h)
    (hz : ∀ l, familyCoefficient zlo zhi J l ∈ Icc (0 : ℝ) 4)
    (hconf : ∀ (A : Finset (Fin n)) (u z : ℝ), u ∈ Icc (0 : ℝ) 1 → z ∈ Icc (0 : ℝ) 4 →
      ν.real {s | h < |estimate y A u z s - (totalEmpiricalInstance y).continuationValue A u 1 z|} ≤ δ)
    (j : Fin (J+1)) :
    (P.worldLaw (policyQueryArrayLaw (n := n) (J := J) ν)).real
      {ω | ∃ i, h < |familyThreshold zlo zhi estimate j (y,ω.2.2) (ω.2.1 i) i
        (history Finset.univ ω.1 ω.2.1 (ω.2.1 i)) -
          (totalEmpiricalInstance y).continuationAtArrival 1 (familyCoefficient zlo zhi J j.val) ω.1 ω.2.1 i|} ≤
      (n : ℝ)*(J+1)*δ := by
  let Q := totalEmpiricalInstance y
  have hQ := totalEmpiricalInstance_integrable y
  refine le_trans (measureReal_mono
    (μ := P.worldLaw (policyQueryArrayLaw (n := n) (J := J) ν)) (s₂ :=
      {ω | ∃ (i : Fin n) (l : Fin (J+1)), h < policyQueryError zlo zhi estimate y i l ω})
      ?_ (measure_ne_top _ _))
    (policyQueryFailure_probability_le P ν zlo zhi estimate hm y hy (fun l => hz l.val) hconf)
  intro ω hω
  by_contra hbad
  obtain ⟨i, hi⟩ := hω
  let H := history Finset.univ ω.1 ω.2.1 (ω.2.1 i)
  let A := (unseen H).erase i
  let d := max 0 (1-ω.2.1 i)
  let v : ℕ → ℝ := fun l => Q.continuationAtArrival 1 (familyCoefficient zlo zhi J l) ω.1 ω.2.1 i
  have hmono : Monotone v := by
    intro a b hab
    change optimalScalarValue (Q.restrictTo A) 1 (familyCoefficient zlo zhi J a*d) ≤
      optimalScalarValue (Q.restrictTo A) 1 (familyCoefficient zlo zhi J b*d)
    exact optimalScalarValue_mono (Q.restrictTo A) (Q.restrictTo_integrable_maximum A hQ)
      zero_le_one (mul_nonneg (hz a).1 (le_max_left _ _)) le_rfl
      (mul_le_mul_of_nonneg_right (familyCoefficient_monotone hord J hab) (le_max_left _ _))
  have hfloor : familyCoefficient zlo zhi J j.val*unitRemaining (ω.2.1 i) ≤ v j.val := by
    calc
      _ ≤ familyCoefficient zlo zhi J j.val*d := mul_le_mul_of_nonneg_left
        (max_le_max le_rfl (min_le_right _ _)) (hz j.val).1
      _ ≤ _ := Q.durationWeight_le_continuationValue hQ A (le_max_left _ _) zero_le_one (hz j.val).1
  have hacc (l : ℕ) (hl : l ≤ j.val) :
      |familyQuery zlo zhi estimate (y,ω.2.2) (ω.2.1 i) i H l-v l| ≤ h := by
    apply le_of_not_gt
    intro he
    have hj := j.isLt
    exact hbad ⟨i, ⟨l, by omega⟩, he⟩
  have hgood := nestedContinuation_error (familyCoefficient zlo zhi J)
    (familyQuery zlo zhi estimate (y,ω.2.2) (ω.2.1 i) i H) v
    (unitRemaining (ω.2.1 i)) j.val hh hmono hfloor hacc
  exact not_lt_of_ge hgood hi

end ProphetSecretary.Statistics.Calibration
