import ProphetSecretary.Limiting.HybridRewardTail
import ProphetSecretary.Limiting.CampbellUnionBound
import ProphetSecretary.Limiting.ConfigurationSetMeasurability
import ProphetSecretary.Stability.TerminalWindow

/-!
# Unconditional hybrid rewards in a terminal time window

Every actual retained and anonymous arrival is counted, including arrivals
following a policy's stopping time. Clock independence and Campbell's formula
give a positive-level tail bound without a retained-dimension or total-rate
factor.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def hybridLateMaximum (cut : ℝ) (v : HybridWorld n Seed) : ℝ :=
  Model.lateMaximum (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) cut

def hybridLateTailEvent (window d : ℝ) : Set (HybridWorld n Seed) :=
  {v | ∃ k : Fin (n+v.1.1), 1-window ≤ combinedClocks v.2.2.1 v.1.2 k ∧
    d < combinedValues v.2.1 v.1.2 k}

omit [MeasurableSpace Seed] in
lemma hybridLateTailEvent_eq_union (window d : ℝ) :
    (hybridLateTailEvent window d : Set (HybridWorld n Seed)) =
      (Prod.snd ⁻¹' {z : Model.World n Seed | ∃ i : Fin n, 1-window ≤ z.2.1 i ∧ d < z.1 i}) ∪
      (Prod.fst ⁻¹' {ω : Configuration | ∃ j : Fin ω.1, ω.2 j ∈ Ici (1-window) ×ˢ Ioi d}) := by
  ext v
  constructor
  · rintro ⟨k,ht,hx⟩
    induction k using Fin.addCases with
    | left i => exact Or.inl ⟨i,
        by simpa only [combinedClocks,Fin.addCases_left] using ht,
        by simpa only [combinedValues,Fin.addCases_left] using hx⟩
    | right j => exact Or.inr ⟨j,
        by simpa only [combinedClocks,Fin.addCases_right,Set.mem_Ici] using ht,
        by simpa only [combinedValues,Fin.addCases_right,Set.mem_Ioi] using hx⟩
  · rintro (⟨i,ht,hx⟩|⟨j,ht,hx⟩)
    · refine ⟨i.castAdd v.1.1,?_,?_⟩
      · simpa only [combinedClocks,Fin.addCases_left] using ht
      · simpa only [combinedValues,Fin.addCases_left] using hx
    · refine ⟨j.natAdd n,?_,?_⟩
      · simpa only [combinedClocks,Fin.addCases_right,Set.mem_Ici] using ht
      · simpa only [combinedValues,Fin.addCases_right,Set.mem_Ioi] using hx

lemma measurableSet_hybridLateTailEvent (window d : ℝ) :
    MeasurableSet (hybridLateTailEvent window d : Set (HybridWorld n Seed)) := by
  rw [hybridLateTailEvent_eq_union]
  apply MeasurableSet.union
  · apply MeasurableSet.preimage _ measurable_snd
    rw [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    exact (measurableSet_le measurable_const
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))).inter
      (measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_fst))
  · exact (measurableSet_exists_configuration_point (measurableSet_Ici.prod measurableSet_Ioi)).preimage measurable_fst

lemma FiniteIntensityHybridInstance.hybridLateTailEvent_probability
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {window : ℝ} (hw0 : 0 ≤ window) (hw1 : window ≤ 1) (d : ℝ) :
    (B.law ν).real (hybridLateTailEvent window d) ≤ window*B.tailCount d := by
  let R : Set (Model.World n Seed) := {z | ∃ i : Fin n, 1-window ≤ z.2.1 i ∧ d < z.1 i}
  let A : Set Configuration := {ω | ∃ j : Fin ω.1, ω.2 j ∈ Ici (1-window) ×ˢ Ioi d}
  have hR : MeasurableSet R := by
    dsimp only [R]
    rw [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    exact (measurableSet_le measurable_const
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))).inter
      (measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_fst))
  have hA : MeasurableSet A := measurableSet_exists_configuration_point (measurableSet_Ici.prod measurableSet_Ioi)
  have hRprob : (B.individuals.worldLaw ν).real R ≤ window*B.individuals.tailCount d := by
    have hEq : R = ⋃ i : Fin n, {z : Model.World n Seed | 1-window ≤ z.2.1 i ∧ d < z.1 i} := Set.setOf_exists _
    rw [hEq]
    calc
      _ ≤ ∑ i : Fin n, (B.individuals.worldLaw ν).real {z | 1-window ≤ z.2.1 i ∧ d < z.1 i} :=
        measureReal_iUnion_fintype_le _
      _ = _ := by
        simp only [B.individuals.world_lateTail_probability ν _ hw0 hw1 d]
        rw [← Finset.mul_sum]
        rfl
  have hAprob : (configurationLaw B.intensity).real A ≤ window*(B.intensity : Measure ℝ).real (Ioi d) := by
    have hRect : MeasurableSet (Ici (1-window) ×ˢ Ioi d) := measurableSet_Ici.prod measurableSet_Ioi
    have h := probability_exists_configuration_point_le_intensity B.intensity hRect
    have hReal := ENNReal.toReal_mono (measure_ne_top (ProphetSecretary.Limiting.intensity B.intensity) _) h
    change (configurationLaw B.intensity).real A ≤
      (Model.Instance.uniformClock.prod (B.intensity : Measure ℝ)).real (Ici (1-window) ×ˢ Ioi d) at hReal
    rw [measureReal_prod_prod,Model.Instance.uniformClock_probability_ge (by linarith : 0 ≤ 1-window)
      (by linarith : 1-window ≤ 1)] at hReal
    convert hReal using 1
    ring
  have hMP₁ : MeasurePreserving (Prod.fst : HybridWorld n Seed → Configuration)
      (B.law ν) (configurationLaw B.intensity) := measurePreserving_fst
  have hMP₂ : MeasurePreserving (Prod.snd : HybridWorld n Seed → Model.World n Seed)
      (B.law ν) (B.individuals.worldLaw ν) := measurePreserving_snd
  have hMarg₁ : (B.law ν).real (Prod.fst ⁻¹' A) = (configurationLaw B.intensity).real A :=
    congrArg ENNReal.toReal (hMP₁.measure_preimage hA.nullMeasurableSet)
  have hMarg₂ : (B.law ν).real (Prod.snd ⁻¹' R) = (B.individuals.worldLaw ν).real R :=
    congrArg ENNReal.toReal (hMP₂.measure_preimage hR.nullMeasurableSet)
  rw [hybridLateTailEvent_eq_union]
  calc
    _ ≤ (B.law ν).real (Prod.snd ⁻¹' R)+(B.law ν).real (Prod.fst ⁻¹' A) := measureReal_union_le _ _
    _ ≤ window*B.individuals.tailCount d+window*(B.intensity : Measure ℝ).real (Ioi d) := by
      rw [hMarg₁,hMarg₂]
      exact add_le_add hRprob hAprob
    _ = _ := by unfold FiniteIntensityHybridInstance.tailCount; ring

lemma measurable_hybridLateMaximum (cut : ℝ) : Measurable (hybridLateMaximum (n := n) (Seed := Seed) cut) := by
  apply measurable_of_configuration_prod_branches
  intro N
  exact Model.measurable_lateMaximum
    (fun k => measurable_combinedValues_family _ (fun i => by fun_prop) _
      (fun j => (measurable_pi_apply j).comp measurable_fst) k)
    (fun k => measurable_combinedClocks_family _ (fun i => by fun_prop) _
      (fun j => (measurable_pi_apply j).comp measurable_fst) k) measurable_const

omit [MeasurableSpace Seed] in
lemma hybridLateMaximum_le_indicator {H d window : ℝ} (hH : 0 ≤ H) (hd : 0 ≤ d)
    (v : HybridWorld n Seed) (hCap : ∀ k, combinedValues v.2.1 v.1.2 k ≤ H) :
    hybridLateMaximum (1-window) v ≤ d+H*(if v ∈ hybridLateTailEvent window d then 1 else 0) := by
  by_cases h : v ∈ hybridLateTailEvent window d
  · rw [if_pos h,mul_one]
    exact (Model.lateMaximum_le _ _ _ hH hCap).trans (by linarith)
  · rw [if_neg h,mul_zero,add_zero]
    apply Model.Instance.maximum_le _ hd
    intro k
    split_ifs with ht
    · by_contra hx
      exact h ⟨k,ht,lt_of_not_ge hx⟩
    · exact hd

lemma FiniteIntensityHybridInstance.integrable_hybridLateMaximum
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (cut : ℝ) :
    Integrable (hybridLateMaximum cut) (B.law ν) := by
  apply Integrable.of_bound (measurable_hybridLateMaximum cut).aestronglyMeasurable (B.cap : ℝ)
  filter_upwards [realized_values_bounds B.individuals B.intensity ν B.individual_bounded B.intensity_supported] with v hv
  have hn : 0 ≤ hybridLateMaximum cut v := Model.lateMaximum_nonnegative _ _ _
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  exact Model.lateMaximum_le _ _ _ B.cap.property (fun k => (hv k).2)

theorem FiniteIntensityHybridInstance.integral_hybridLateMaximum_le
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {H d window : ℝ} (hH : 0 ≤ H) (hCap : (B.cap : ℝ) ≤ H) (hd : 0 ≤ d)
    (hw0 : 0 ≤ window) (hw1 : window ≤ 1) :
    (∫ v, hybridLateMaximum (1-window) v ∂B.law ν) ≤ d+H*window*B.tailCount d := by
  let E : Set (HybridWorld n Seed) := hybridLateTailEvent window d
  let I : HybridWorld n Seed → ℝ := E.indicator (fun _ => 1)
  have hE : MeasurableSet E := measurableSet_hybridLateTailEvent window d
  have hI : Integrable I (B.law ν) := (integrable_const (1 : ℝ)).indicator hE
  have hEq : (∫ v, I v ∂B.law ν) = (B.law ν).real E := integral_indicator_one hE
  have hBound := integral_mono_ae (B.integrable_hybridLateMaximum ν (1-window))
    ((integrable_const d).add (hI.const_mul H)) (by
      filter_upwards [realized_values_bounds B.individuals B.intensity ν B.individual_bounded B.intensity_supported] with v hv
      change hybridLateMaximum (1-window) v ≤ d+H*I v
      simpa only [I,E,Set.indicator_apply,Pi.one_apply] using
        hybridLateMaximum_le_indicator hH hd v (fun k => ((hv k).2).trans hCap))
  change (∫ v, hybridLateMaximum (1-window) v ∂B.law ν) ≤
    ∫ v, d+H*I v ∂B.law ν at hBound
  rw [integral_add (integrable_const d) (hI.const_mul H),integral_const_mul,hEq] at hBound
  simp only [integral_const,probReal_univ,one_smul] at hBound
  have hP := mul_le_mul_of_nonneg_left (B.hybridLateTailEvent_probability ν hw0 hw1 d) hH
  dsimp only [E] at hBound
  nlinarith only [hBound,hP]

end ProphetSecretary.Limiting
