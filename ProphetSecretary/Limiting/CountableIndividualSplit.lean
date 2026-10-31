import ProphetSecretary.Limiting.CountablePrefixLaw
import ProphetSecretary.Probability.PrefixTailIndependence

/-!
# Actual prefix--tail splitting and reconstruction of individual values

The full infinite tail is independent of the observed prefix. Its product law
and the measurable inverse splice are constructed. The same facts hold for
arrival clocks, supplying genuine independent auxiliary data to omission
simulation rather than an assumed independence interface.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def splitCoordinates (N : ℕ) (x : ℕ → ℝ) : (Fin N → ℝ) × (ℕ → ℝ) :=
  ((fun i => x i.val),fun j => x (j+N))

noncomputable def splicePrefix {N : ℕ} (x : Fin N → ℝ) (z : ℕ → ℝ) (i : ℕ) : ℝ :=
  if hi : i < N then x ⟨i,hi⟩ else z (i-N)

lemma measurable_splitCoordinates (N : ℕ) : Measurable (splitCoordinates N) :=
  (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)).prodMk
    (measurable_pi_lambda _ (fun j => measurable_pi_apply (j+N)))

lemma measurable_splicePrefix (N : ℕ) :
    Measurable (fun q : (Fin N → ℝ) × (ℕ → ℝ) => splicePrefix q.1 q.2) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i < N
  · simp only [splicePrefix,dif_pos hi]
    exact (measurable_pi_apply (⟨i,hi⟩ : Fin N)).comp measurable_fst
  · simp only [splicePrefix,dif_neg hi]
    exact (measurable_pi_apply (i-N)).comp measurable_snd

lemma splice_splitCoordinates (N : ℕ) (x : ℕ → ℝ) :
    splicePrefix (splitCoordinates N x).1 (splitCoordinates N x).2 = x := by
  funext i
  by_cases hi : i < N
  · simp only [splicePrefix,dif_pos hi,splitCoordinates]
  · simp only [splicePrefix,dif_neg hi,splitCoordinates]
    rw [Nat.sub_add_cancel (Nat.le_of_not_gt hi)]

lemma split_splicePrefix (N : ℕ) (q : (Fin N → ℝ) × (ℕ → ℝ)) :
    splitCoordinates N (splicePrefix q.1 q.2) = q := by
  apply Prod.ext
  · funext i
    simp only [splitCoordinates,splicePrefix,dif_pos i.isLt]
  · funext j
    have hj : ¬j+N < N := by omega
    simp only [splitCoordinates,splicePrefix,dif_neg hj,Nat.add_sub_cancel]

noncomputable def prefixTailEquiv (N : ℕ) : (ℕ → ℝ) ≃ᵐ ((Fin N → ℝ) × (ℕ → ℝ)) where
  toEquiv := ⟨splitCoordinates N,fun q => splicePrefix q.1 q.2,splice_splitCoordinates N,split_splicePrefix N⟩
  measurable_toFun := measurable_splitCoordinates N
  measurable_invFun := measurable_splicePrefix N

variable (B : CountableInstance)

noncomputable def tailValuesLaw (N : ℕ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun j => (B.individuals (j+N) : Measure ℝ))

instance tailValuesLaw_probability (N : ℕ) : IsProbabilityMeasure (B.tailValuesLaw N) := by
  unfold tailValuesLaw
  infer_instance

lemma tailValues_measurePreserving (N : ℕ) :
    MeasurePreserving (fun x : ℕ → ℝ => fun j : ℕ => x (j+N)) B.individualValuesLaw (B.tailValuesLaw N) := by
  refine ⟨measurable_pi_lambda _ (fun j => measurable_pi_apply (j+N)),?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun i j h => Nat.add_right_cancel h)

lemma prefix_tail_values_independent (N : ℕ) :
    IndepFun (fun x : ℕ → ℝ => fun i : Fin N => x i.val)
      (fun x : ℕ → ℝ => fun j : ℕ => x (j+N)) B.individualValuesLaw :=
  ProphetSecretary.Probability.indepFun_prefix_tail B.individualValues_independent
    (fun i => measurable_pi_apply i) N

lemma splitValues_measurePreserving (N : ℕ) :
    MeasurePreserving (splitCoordinates N) B.individualValuesLaw
      ((B.individualPrefix N).valuesLaw.prod (B.tailValuesLaw N)) := by
  refine ⟨measurable_splitCoordinates N,?_⟩
  have he := (B.prefix_tail_values_independent N).map_prod_eq_prod_map_map
    (B.prefixValues_measurePreserving N).measurable.aemeasurable
    (B.tailValues_measurePreserving N).measurable.aemeasurable
  rw [(B.prefixValues_measurePreserving N).map_eq,(B.tailValues_measurePreserving N).map_eq] at he
  exact he

lemma spliceValues_measurePreserving (N : ℕ) :
    MeasurePreserving (fun q : (Fin N → ℝ) × (ℕ → ℝ) => splicePrefix q.1 q.2)
      ((B.individualPrefix N).valuesLaw.prod (B.tailValuesLaw N)) B.individualValuesLaw :=
  (B.splitValues_measurePreserving N).symm (prefixTailEquiv N)

lemma tailClocks_measurePreserving (N : ℕ) :
    MeasurePreserving (fun u : ℕ → ℝ => fun j : ℕ => u (j+N)) individualClocksLaw individualClocksLaw := by
  refine ⟨measurable_pi_lambda _ (fun j => measurable_pi_apply (j+N)),?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun i j h => Nat.add_right_cancel h)

lemma prefix_tail_clocks_independent (N : ℕ) :
    IndepFun (fun u : ℕ → ℝ => fun i : Fin N => u i.val)
      (fun u : ℕ → ℝ => fun j : ℕ => u (j+N)) individualClocksLaw :=
  ProphetSecretary.Probability.indepFun_prefix_tail individualClocks_independent
    (fun i => measurable_pi_apply i) N

lemma splitClocks_measurePreserving (N : ℕ) :
    MeasurePreserving (splitCoordinates N) individualClocksLaw
      ((Model.Instance.clocksLaw N).prod individualClocksLaw) := by
  refine ⟨measurable_splitCoordinates N,?_⟩
  have he := (prefix_tail_clocks_independent N).map_prod_eq_prod_map_map
    (prefixClocks_measurePreserving N).measurable.aemeasurable
    (tailClocks_measurePreserving N).measurable.aemeasurable
  rw [(prefixClocks_measurePreserving N).map_eq,(tailClocks_measurePreserving N).map_eq] at he
  exact he

lemma spliceClocks_measurePreserving (N : ℕ) :
    MeasurePreserving (fun q : (Fin N → ℝ) × (ℕ → ℝ) => splicePrefix q.1 q.2)
      ((Model.Instance.clocksLaw N).prod individualClocksLaw) individualClocksLaw :=
  (splitClocks_measurePreserving N).symm (prefixTailEquiv N)

end ProphetSecretary.Limiting.CountableInstance
