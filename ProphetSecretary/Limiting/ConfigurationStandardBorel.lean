import ProphetSecretary.Limiting.CountableCandidates
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The actual configuration space is standard Borel

A finite array is represented by its length and an infinite array padded by a
fixed point. The padding condition is Borel. This proves the hypotheses needed
for analytical conditional couplings without any restriction on policy seeds.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

abbrev PaddedArrays := ℕ × (ℕ → Point)

def ProperPadding (q : PaddedArrays) : Prop := ∀ j, q.1 ≤ j → q.2 j = ((1 : ℝ),(0 : ℝ))

lemma measurableSet_properPadding : MeasurableSet {q : PaddedArrays | ProperPadding q} := by
  unfold ProperPadding
  simp only [setOf_forall,imp_iff_not_or,setOf_or,← compl_setOf]
  apply MeasurableSet.iInter
  intro j
  exact (measurableSet_le measurable_fst measurable_const).compl.union
    (measurableSet_eq_fun ((measurable_pi_apply j).comp measurable_snd) measurable_const)

noncomputable def padConfiguration (ω : Configuration) : {q : PaddedArrays // ProperPadding q} :=
  ⟨(ω.1,fun j => configurationPoint j ω),by
    intro j hj
    exact dif_neg (Nat.not_lt_of_ge hj)⟩

noncomputable def unpadArray (q : PaddedArrays) : Configuration :=
  configurationMk q.1 (fun j : Fin q.1 => q.2 j.val)

lemma measurable_padConfiguration : Measurable padConfiguration :=
  (measurable_configuration_count.prodMk (measurable_pi_lambda _ (fun j => measurable_configurationPoint j))).subtype_mk

lemma measurable_unpadArray : Measurable unpadArray := by
  apply measurable_from_prod_countable_right
  intro N
  exact (measurable_configuration_mk N).comp
    (measurable_pi_lambda _ (fun j : Fin N => measurable_pi_apply j.val))

lemma unpad_padConfiguration (ω : Configuration) : unpadArray (padConfiguration ω).1 = ω := by
  rcases ω with ⟨N,v⟩
  change configurationMk N (fun j : Fin N => configurationPoint j.val ⟨N,v⟩) = configurationMk N v
  congr 1
  funext j
  exact dif_pos j.isLt

lemma pad_unpadArray (q : {q : PaddedArrays // ProperPadding q}) :
    padConfiguration (unpadArray q.1) = q := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext j
    by_cases hj : j < q.1.1
    · exact dif_pos hj
    · change configurationPoint j (unpadArray q.1) = q.1.2 j
      simp only [configurationPoint,unpadArray,configurationMk,dif_neg hj]
      exact (q.2 j (Nat.le_of_not_gt hj)).symm

noncomputable def configurationPaddingEquiv : Configuration ≃ᵐ {q : PaddedArrays // ProperPadding q} where
  toEquiv := ⟨padConfiguration,fun q => unpadArray q.1,unpad_padConfiguration,pad_unpadArray⟩
  measurable_toFun := measurable_padConfiguration
  measurable_invFun := measurable_unpadArray.comp measurable_subtype_coe

private lemma standardBorel_of_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace β] (e : α ≃ᵐ β) : StandardBorelSpace α := by
  letI := upgradeStandardBorel β
  letI : TopologicalSpace α := TopologicalSpace.induced e inferInstance
  haveI : BorelSpace α := e.measurableEmbedding.borelSpace ⟨rfl⟩
  haveI : PolishSpace α := e.toEquiv.polishSpace_induced
  infer_instance

instance configuration_standardBorel : StandardBorelSpace Configuration := by
  haveI : StandardBorelSpace {q : PaddedArrays // ProperPadding q} := measurableSet_properPadding.standardBorel
  exact standardBorel_of_measurableEquiv configurationPaddingEquiv

instance bandConfigurations_standardBorel : StandardBorelSpace BandConfigurations := inferInstance

end ProphetSecretary.Limiting
