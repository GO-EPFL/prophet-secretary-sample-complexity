import ProphetSecretary.Limiting.CountableIndividualSplit

/-!
# Actual online-law transport for omitted-individual auxiliary samples

Independent tail values and clocks can be moved into a policy's auxiliary
seed. The displayed reconstruction map has the original countable online
law, including the independent original seed; this is a proved product-law
identity rather than an independence assumption on a simulator interface.
-/

open MeasureTheory

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def augmentIndividualsWorld {N : ℕ} {Seed : Type*}
    (v : Model.World N (Seed × ((ℕ → ℝ) × (ℕ → ℝ)))) : (ℕ → ℝ) × ((ℕ → ℝ) × Seed) :=
  (splicePrefix v.1 v.2.2.2.1,(splicePrefix v.2.1 v.2.2.2.2,v.2.2.1))

lemma augmentIndividualsWorld_measurePreserving (B : CountableInstance) {Seed : Type*}
    [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] (N : ℕ) :
    MeasurePreserving (augmentIndividualsWorld (N := N))
      ((B.individualPrefix N).worldLaw (ν.prod ((B.tailValuesLaw N).prod individualClocksLaw)))
      (B.individualWorldLaw ν) := by
  let μx := (B.individualPrefix N).valuesLaw
  let μu := Model.Instance.clocksLaw N
  let μz := B.tailValuesLaw N
  let μv := individualClocksLaw
  have h₁ := (MeasurePreserving.id μx).prod
    ((MeasurePreserving.id μu).prod (Measure.measurePreserving_swap (μ := ν) (ν := μz.prod μv)))
  have h₂ := (MeasurePreserving.id μx).prod
    ((measurePreserving_prodAssoc μu (μz.prod μv) ν).symm MeasurableEquiv.prodAssoc)
  have ha := (measurePreserving_prodAssoc μu μz μv).symm MeasurableEquiv.prodAssoc
  have hb := (Measure.measurePreserving_swap (μ := μu) (ν := μz)).prod (MeasurePreserving.id μv)
  have hc := measurePreserving_prodAssoc μz μu μv
  have h₃ := (MeasurePreserving.id μx).prod ((hc.comp (hb.comp ha)).prod (MeasurePreserving.id ν))
  have h₄ := (measurePreserving_prodAssoc μx (μz.prod (μu.prod μv)) ν).symm MeasurableEquiv.prodAssoc
  have h₅ := ((measurePreserving_prodAssoc μx μz (μu.prod μv)).symm MeasurableEquiv.prodAssoc).prod
    (MeasurePreserving.id ν)
  have h₆ := ((B.spliceValues_measurePreserving N).prod (spliceClocks_measurePreserving N)).prod
    (MeasurePreserving.id ν)
  have h₇ := measurePreserving_prodAssoc B.individualValuesLaw individualClocksLaw ν
  exact h₇.comp (h₆.comp (h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))))

noncomputable def splitIndividualsWorld (N : ℕ) {Seed : Type*}
    (v : (ℕ → ℝ) × ((ℕ → ℝ) × Seed)) : Model.World N (Seed × ((ℕ → ℝ) × (ℕ → ℝ))) :=
  ((splitCoordinates N v.1).1,((splitCoordinates N v.2.1).1,
    (v.2.2,((splitCoordinates N v.1).2,(splitCoordinates N v.2.1).2))))

lemma augment_splitIndividualsWorld (N : ℕ) {Seed : Type*} (v : (ℕ → ℝ) × ((ℕ → ℝ) × Seed)) :
    augmentIndividualsWorld (splitIndividualsWorld N v) = v := by
  change (splicePrefix (splitCoordinates N v.1).1 (splitCoordinates N v.1).2,
    (splicePrefix (splitCoordinates N v.2.1).1 (splitCoordinates N v.2.1).2,v.2.2)) = v
  rw [splice_splitCoordinates,splice_splitCoordinates]

lemma split_augmentIndividualsWorld (N : ℕ) {Seed : Type*}
    (v : Model.World N (Seed × ((ℕ → ℝ) × (ℕ → ℝ)))) :
    splitIndividualsWorld N (augmentIndividualsWorld v) = v := by
  unfold splitIndividualsWorld augmentIndividualsWorld
  rw [split_splicePrefix N (v.1,v.2.2.2.1),split_splicePrefix N (v.2.1,v.2.2.2.2)]

lemma measurable_splitIndividualsWorld (N : ℕ) {Seed : Type*} [MeasurableSpace Seed] :
    Measurable (splitIndividualsWorld (Seed := Seed) N) := by
  have hx := (measurable_splitCoordinates N).comp
    (measurable_fst : Measurable (fun v : (ℕ → ℝ) × ((ℕ → ℝ) × Seed) => v.1))
  have hu := (measurable_splitCoordinates N).comp
    (show Measurable (fun v : (ℕ → ℝ) × ((ℕ → ℝ) × Seed) => v.2.1) by fun_prop)
  have hr : Measurable (fun v : (ℕ → ℝ) × ((ℕ → ℝ) × Seed) => v.2.2) := by fun_prop
  exact (measurable_fst.comp hx).prodMk ((measurable_fst.comp hu).prodMk
    (hr.prodMk ((measurable_snd.comp hx).prodMk (measurable_snd.comp hu))))

lemma measurable_augmentIndividualsWorld (N : ℕ) {Seed : Type*} [MeasurableSpace Seed] :
    Measurable (augmentIndividualsWorld (N := N) (Seed := Seed)) := by
  have hx : Measurable (fun v : Model.World N (Seed × ((ℕ → ℝ) × (ℕ → ℝ))) => splicePrefix v.1 v.2.2.2.1) :=
    (measurable_splicePrefix N).comp (measurable_fst.prodMk (by fun_prop))
  have hup : Measurable (fun v : Model.World N (Seed × ((ℕ → ℝ) × (ℕ → ℝ))) => v.2.1) := by fun_prop
  have hut : Measurable (fun v : Model.World N (Seed × ((ℕ → ℝ) × (ℕ → ℝ))) => v.2.2.2.2) := by fun_prop
  have hu : Measurable (fun v : Model.World N (Seed × ((ℕ → ℝ) × (ℕ → ℝ))) => splicePrefix v.2.1 v.2.2.2.2) :=
    (measurable_splicePrefix N).comp (hup.prodMk hut)
  have hr : Measurable (fun v : Model.World N (Seed × ((ℕ → ℝ) × (ℕ → ℝ))) => v.2.2.1) := by fun_prop
  exact hx.prodMk (hu.prodMk hr)

noncomputable def individualsWorldEquiv (N : ℕ) (Seed : Type*) [MeasurableSpace Seed] :
    Model.World N (Seed × ((ℕ → ℝ) × (ℕ → ℝ))) ≃ᵐ ((ℕ → ℝ) × ((ℕ → ℝ) × Seed)) where
  toEquiv := ⟨augmentIndividualsWorld,splitIndividualsWorld N,
    split_augmentIndividualsWorld N,augment_splitIndividualsWorld N⟩
  measurable_toFun := measurable_augmentIndividualsWorld N
  measurable_invFun := measurable_splitIndividualsWorld N

lemma splitIndividualsWorld_measurePreserving (B : CountableInstance) {Seed : Type*}
    [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] (N : ℕ) :
    MeasurePreserving (splitIndividualsWorld N) (B.individualWorldLaw ν)
      ((B.individualPrefix N).worldLaw (ν.prod ((B.tailValuesLaw N).prod individualClocksLaw))) :=
  (B.augmentIndividualsWorld_measurePreserving ν N).symm (individualsWorldEquiv N Seed)

end ProphetSecretary.Limiting.CountableInstance
