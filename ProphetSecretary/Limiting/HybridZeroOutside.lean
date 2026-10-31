import ProphetSecretary.Limiting.HybridRetainedMonotonicity

/-!
# Independent zero identities outside a retained hybrid state

Zero identities remain observable. Their value invariance is proved using the
actual finite Bernoulli approximants and the finite causal zero simulation;
it is not assumed as an erasure interface. The explicit masked instance keeps
its original dimension, arrival clocks, anonymous intensity and terminal data.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma FiniteIntensityHybridInstance.optimalScalarValue_eq_of_data
    (B D : FiniteIntensityHybridInstance n) (hP : B.individuals = D.individuals)
    (hμ : B.intensity = D.intensity) (ha : B.terminal = D.terminal) (w c : ℝ) :
    B.optimalScalarValue w c = D.optimalScalarValue w c := by
  have hL (π : RandomizedHybridPolicy n) : B.law π.seedLaw = D.law π.seedLaw := by
    unfold FiniteIntensityHybridInstance.law
    rw [hP,hμ]
  have hF : (fun π : RandomizedHybridPolicy n => π.scalarObjective B w c) = fun π => π.scalarObjective D w c := by
    funext π
    unfold RandomizedHybridPolicy.scalarObjective
    rw [ha,hL π]
  unfold FiniteIntensityHybridInstance.optimalScalarValue FiniteIntensityHybridInstance.scalarPayoffs
  rw [hF]

/-- Full-policy value invariance for genuine deterministic-zero marginal
laws outside A, allowing μ=0 and zero expected maximum. -/
theorem FiniteIntensityHybridInstance.optimalScalarValue_eq_restrictIndividuals_of_zero_outside
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (A : Finset (Fin n))
    (hz : ∀ i ∉ A, B.individuals.law i = Measure.dirac 0) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c = (B.restrictIndividuals A).optimalScalarValue w c := by
  by_cases hμ : B.intensity = 0
  · rw [B.value_zero_intensity ha hμ hw hc,(B.restrictIndividuals A).value_zero_intensity ha hμ hw hc]
    exact B.individuals.optimalScalarValue_eq_restrictTo_of_zero_outside A
      (B.individuals.integrable_maximum_of_bounded B.individual_bounded) hz hw hc
  by_cases hw0 : w = 0
  · subst w
    rw [B.value_zero_rewardWeight hc,(B.restrictIndividuals A).value_zero_rewardWeight hc]
  have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hFinite (j : ℕ) :
      Model.optimalScalarValue (B.bernoulliApproximation hμ j) w c =
      Model.optimalScalarValue ((B.restrictIndividuals A).bernoulliApproximation hμ j) w c := by
    let rate := (B.intensity : Measure ℝ).real univ
    let q := bernoulliMultiplicity rate j
    let p := bernoulliProbability rate measureReal_nonneg j
    let κ : Measure ℝ := B.intensity.normalize
    let hκ := B.normalizedMark_nonnegative hμ
    let Q := finitePoissonDesign B.individuals κ hκ p q
    let S := completeVirtualState q A
    have hQ := finitePoissonDesign_integrable_maximum B.individuals κ hκ p q
      (B.individuals.integrable_maximum_of_bounded B.individual_bounded) (B.normalizedMark_integrable hμ)
    have hzQ (k : Fin (n+q)) (hk : k ∉ S) : Q.law k = Measure.dirac 0 := by
      induction k using Fin.addCases with
      | left i =>
        have hi : i ∉ A := fun hi => hk ((mem_completeVirtualState_left A i).mpr hi)
        simpa only [Q,finitePoissonDesign,appendIID,Fin.addCases_left] using hz i hi
      | right k => exact False.elim (hk (mem_completeVirtualState_right A k))
    have hDrop := Q.optimalScalarValue_eq_restrictTo_of_zero_outside S hQ hzQ hw hc
    have hRelabel := appendIID_restrictTo_value B.individuals (zeroInflatedLaw κ p)
      (zeroInflatedLaw_nonnegative κ hκ p) q S hQ hw hc
    change Model.optimalScalarValue (Q.restrictTo S) w c =
      Model.optimalScalarValue (finitePoissonDesign (B.individuals.restrictTo (Model.retainedSet q S)) κ hκ p (virtualSet n S).card) w c at hRelabel
    rw [completeVirtualState_retained,completeVirtualState_virtual] at hRelabel
    simp only [Finset.card_univ] at hRelabel
    have hCard : Fintype.card (Fin q) = q := Fintype.card_fin q
    rw [hCard] at hRelabel
    exact hDrop.trans hRelabel
  have hFull := B.bernoulliApproximation_value_tendsto ha hμ hwP hc
  have hSub := (B.restrictIndividuals A).bernoulliApproximation_value_tendsto ha hμ hwP hc
  simp_rw [hFinite] at hFull
  exact tendsto_nhds_unique hFull hSub

noncomputable def FiniteIntensityHybridInstance.zeroOutside (B : FiniteIntensityHybridInstance n) (A : Finset (Fin n)) :
    FiniteIntensityHybridInstance n where
  cap := B.cap
  terminal := B.terminal
  terminal_le_cap := B.terminal_le_cap
  individuals := {
    law := fun i => if i ∈ A then B.individuals.law i else Measure.dirac 0
    probability := by intro i; split_ifs <;> infer_instance
    nonnegative := by intro i; split_ifs; exact B.individuals.nonnegative i; simp }
  individual_bounded := by
    intro i
    change ∀ᵐ x ∂(if i ∈ A then B.individuals.law i else Measure.dirac 0), x ≤ (B.cap : ℝ)
    split_ifs
    · exact B.individual_bounded i
    · simp
  intensity := B.intensity
  intensity_supported := B.intensity_supported

/-- Replacing seen coordinates by fresh independent deterministic-zero laws
has exactly the retained-subset value, while their zero arrivals stay observed. -/
theorem FiniteIntensityHybridInstance.zeroOutside_value_eq_restrictIndividuals
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (A : Finset (Fin n))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (B.zeroOutside A).optimalScalarValue w c = (B.restrictIndividuals A).optimalScalarValue w c := by
  have hz (i : Fin n) (hi : i ∉ A) : (B.zeroOutside A).individuals.law i = Measure.dirac 0 := by
    simp only [FiniteIntensityHybridInstance.zeroOutside,if_neg hi]
  have hValue := (B.zeroOutside A).optimalScalarValue_eq_restrictIndividuals_of_zero_outside ha A hz hw hc
  have hP : ((B.zeroOutside A).restrictIndividuals A).individuals = (B.restrictIndividuals A).individuals := by
    apply Model.Instance.eq_of_law_eq
    funext i
    change (if Model.stateEmbedding A i ∈ A then B.individuals.law (Model.stateEmbedding A i) else Measure.dirac 0) = _
    have hi : Model.stateEmbedding A i ∈ A := A.orderEmbOfFin_mem rfl i
    rw [if_pos hi]
    rfl
  exact hValue.trans (((B.zeroOutside A).restrictIndividuals A).optimalScalarValue_eq_of_data
    (B.restrictIndividuals A) hP rfl rfl w c)

/-- The same invariance holds at every allowed terminal reserve, by exact
reserve removal. All reward and duration weights remain nonnegative. -/
theorem FiniteIntensityHybridInstance.optimalScalarValue_eq_restrictIndividuals_of_zero_outside_with_terminal
    (B : FiniteIntensityHybridInstance n) (A : Finset (Fin n))
    (hz : ∀ i ∉ A, B.individuals.law i = Measure.dirac 0) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c = (B.restrictIndividuals A).optimalScalarValue w c := by
  by_cases hw0 : w = 0
  · subst w
    rw [B.value_zero_rewardWeight hc,(B.restrictIndividuals A).value_zero_rewardWeight hc]
  have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  let C := B.excessState B.terminal
  let D := (B.restrictIndividuals A).excessState B.terminal
  have hzC (i : Fin n) (hi : i ∉ A) : C.individuals.law i = Measure.dirac 0 := by
    change Model.excessLaw (B.individuals.law i) (B.terminal : ℝ) = _
    rw [hz i hi]
    exact Model.excessLaw_dirac_zero B.terminal.property
  have hC := C.optimalScalarValue_eq_restrictIndividuals_of_zero_outside rfl A hzC hw hc
  have hP : (C.restrictIndividuals A).individuals = D.individuals := by
    apply Model.Instance.eq_of_law_eq
    funext i
    rfl
  have hE := (C.restrictIndividuals A).optimalScalarValue_eq_of_data D hP rfl rfl w c
  have hEq := hC.trans hE
  rw [B.value_reserveShift hwP hc,(B.restrictIndividuals A).value_reserveShift hwP hc]
  exact congrArg (fun x : ℝ => w*(B.terminal : ℝ)+x) hEq

/-- Actual zero-masked data, with arbitrary terminal reserve and no positive
benchmark hypothesis. Independent zero arrivals keep their original labels. -/
theorem FiniteIntensityHybridInstance.zeroOutside_value_eq_restrictIndividuals_with_terminal
    (B : FiniteIntensityHybridInstance n) (A : Finset (Fin n)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (B.zeroOutside A).optimalScalarValue w c = (B.restrictIndividuals A).optimalScalarValue w c := by
  have hz (i : Fin n) (hi : i ∉ A) : (B.zeroOutside A).individuals.law i = Measure.dirac 0 := by
    simp only [FiniteIntensityHybridInstance.zeroOutside,if_neg hi]
  have hValue := (B.zeroOutside A).optimalScalarValue_eq_restrictIndividuals_of_zero_outside_with_terminal A hz hw hc
  have hP : ((B.zeroOutside A).restrictIndividuals A).individuals = (B.restrictIndividuals A).individuals := by
    apply Model.Instance.eq_of_law_eq
    funext i
    change (if Model.stateEmbedding A i ∈ A then B.individuals.law (Model.stateEmbedding A i) else Measure.dirac 0) = _
    have hi : Model.stateEmbedding A i ∈ A := A.orderEmbOfFin_mem rfl i
    rw [if_pos hi]
    rfl
  exact hValue.trans (((B.zeroOutside A).restrictIndividuals A).optimalScalarValue_eq_of_data
    (B.restrictIndividuals A) hP rfl rfl w c)

end ProphetSecretary.Limiting
