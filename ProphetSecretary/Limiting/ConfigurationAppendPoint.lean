import ProphetSecretary.Limiting.CountableCandidates

/-!
# Appending one analytical occurrence to a configuration

Old array entries retain their labels. Only the formerly absent last label
becomes present. These labels are analytical and are not policy observations.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
open CountableInstance

def appendConfigurationPoint (ω : Configuration) (p : Point) : Configuration :=
  configurationMk (ω.1+1) (fun j => if hj : j.val<ω.1 then ω.2 ⟨j.val,hj⟩ else p)

lemma appendConfigurationPoint_count (ω : Configuration) (p : Point) :
    (appendConfigurationPoint ω p).1=ω.1+1 := rfl

lemma configurationPoint_append_old (ω : Configuration) (p : Point) (j : ℕ) (hj : j<ω.1) :
    configurationPoint j (appendConfigurationPoint ω p)=configurationPoint j ω := by
  have hj' : j<ω.1+1 := Nat.lt_succ_of_lt hj
  simp only [configurationPoint,appendConfigurationPoint,configurationMk,dif_pos hj',dif_pos hj]

lemma configurationPoint_append_last (ω : Configuration) (p : Point) :
    configurationPoint ω.1 (appendConfigurationPoint ω p)=p := by
  simp only [configurationPoint,appendConfigurationPoint,configurationMk,dif_pos (Nat.lt_succ_self _),lt_self_iff_false,dite_false]

lemma configurationPoint_append_of_ne (ω : Configuration) (p : Point) (j : ℕ) (hj : j≠ω.1) :
    configurationPoint j (appendConfigurationPoint ω p)=configurationPoint j ω := by
  by_cases hOld : j<ω.1
  · exact configurationPoint_append_old ω p j hOld
  · have hNew : ¬j<ω.1+1 := by omega
    simp only [configurationPoint,appendConfigurationPoint,configurationMk,dif_neg hNew,dif_neg hOld]

lemma measurable_appendConfigurationPoint :
    Measurable (fun z : Configuration × Point => appendConfigurationPoint z.1 z.2) := by
  apply measurable_of_configuration_prod_branches
  intro N
  apply (measurable_configuration_mk (N+1)).comp
  apply measurable_pi_lambda
  intro j
  by_cases hj : j.val<N
  · simpa only [appendConfigurationPoint,configurationMk,dif_pos hj,Function.comp_def] using
      (measurable_pi_apply (⟨j.val,hj⟩ : Fin N)).comp
        (measurable_fst : Measurable (fun z : (Fin N → Point) × Point => z.1))
  · simpa only [appendConfigurationPoint,configurationMk,dif_neg hj] using
      (measurable_snd : Measurable (fun z : (Fin N → Point) × Point => z.2))

end ProphetSecretary.Limiting
