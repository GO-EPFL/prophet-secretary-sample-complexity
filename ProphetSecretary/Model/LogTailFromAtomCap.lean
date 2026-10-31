import ProphetSecretary.Model.HighTailMass

/-!
# The logarithmic tail estimate given the aggregate atom cap

The high-tail mass is controlled by the proved response comparison. The
complement is bounded by its closed-tail envelope, including a possible atom
at its lower endpoint. The atom cap is an explicit prerequisite here.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.aggregatePositiveMeasure_Icc_eq_Ici (P : Instance n) (a : ℝ) :
    P.aggregatePositiveMeasure.real (Icc a 1) = P.aggregatePositiveMeasure.real (Ici a) := by
  rw [P.aggregatePositiveMeasure_real_apply measurableSet_Icc,
    P.aggregatePositiveMeasure_real_apply measurableSet_Ici]
  have heq : Icc a 1 ∩ Ioc (0 : ℝ) 1 = Ici a ∩ Ioc (0 : ℝ) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_Ioc, mem_Ici]
    tauto
  rw [heq]

lemma Instance.aggregatePositiveMeasure_Ici_eq_sum (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {a : ℝ} (ha : 0 < a) :
    P.aggregatePositiveMeasure.real (Ici a) = ∑ i, (P.law i).real (Ici a) := by
  rw [P.aggregatePositiveMeasure_real_apply measurableSet_Ici]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (Ici a ∩ Ioc (0 : ℝ) 1 : Set ℝ) =ᵐ[P.law i] (Ici a : Set ℝ) := by
    filter_upwards [hcap i] with x hx
    exact propext ⟨fun h => h.1, fun h => ⟨h, ha.trans_le h, hx⟩⟩
  exact congrArg ENNReal.toReal (measure_congr heq)

/-- The `upmom:logtail` assembly with its atom-cap prerequisite explicit. -/
theorem Instance.logtail_of_atomCap (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c a K : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (he : P.firstMomentError δ h w c ≤ firstMomentSurvivalConstant)
    (ha : 2 * h ≤ a) (hK : 0 < K)
    (hKκ : 2 * optimalCompetitiveRatio * Real.exp 1 / firstMomentSelectionConstant δ ≤ K)
    (hsmall : 2 * (1 + P.totalFirstMoment) * P.valueStationarityError δ h w c ≤
      firstMomentSelectionConstant δ * a)
    (hlog : 0 ≤ Real.log (K * (1 + P.totalFirstMoment) / a) + 2)
    (hatom : ∀ x ∈ Icc a 1, P.aggregateAtomMass x < 2) :
    (∑ i, (P.law i).real (Ici a)) ≤ Real.log (K * (1 + P.totalFirstMoment) / a) + 3 := by
  let T := Real.log (K * (1 + P.totalFirstMoment) / a)
  let B := Icc a 1 ∩ {x | T ≤ P.tailCount x}
  let G := Icc a 1 ∩ {x | P.tailCount x < T}
  let b := firstMomentSelectionConstant δ * a / (2 * (1 + P.totalFirstMoment))
  have ha0 : 0 < a := by linarith only [hh, ha]
  have hS := P.totalFirstMoment_nonnegative
  have hb : 0 < b := div_pos (mul_pos (firstMomentSelectionConstant_positive hδ) ha0)
    (by positivity : 0 < 2 * (1 + P.totalFirstMoment))
  have hmass := P.highTail_mass_discrepancy hcap hδ hwδ hcδ hsum hh hquarter he ha hK hKκ
  change b * P.aggregatePositiveMeasure.real B ≤ P.valueStationarityError δ h w c at hmass
  have hd : P.valueStationarityError δ h w c ≤ b := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (1 + P.totalFirstMoment))).mpr
    nlinarith only [hsmall]
  have hbad : P.aggregatePositiveMeasure.real B ≤ 1 := by
    nlinarith only [hmass, hd, hb]
  have hgood : P.aggregatePositiveMeasure.real G ≤ T + 2 :=
    P.aggregatePositiveMeasure_tailEnvelope hcap ha0 (fun _ hx => hx.1) hlog
      (fun _ hx => hx.2) (fun x hx => hatom x hx.1)
  have hcover : B ∪ G = Icc a 1 := by
    ext x
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      by_cases hT : T ≤ P.tailCount x
      · exact Or.inl ⟨hx, hT⟩
      · exact Or.inr ⟨hx, lt_of_not_ge hT⟩
  have hunion := measureReal_union_le (μ := P.aggregatePositiveMeasure) B G
  rw [hcover, P.aggregatePositiveMeasure_Icc_eq_Ici a, P.aggregatePositiveMeasure_Ici_eq_sum hcap ha0] at hunion
  change (∑ i, (P.law i).real (Ici a)) ≤ T + 3
  linarith only [hunion, hbad, hgood]

end ProphetSecretary.Model
