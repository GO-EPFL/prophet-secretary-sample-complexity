import ProphetSecretary.Limiting.HybridBranchLaw
import ProphetSecretary.Limiting.ConfigurationSetMeasurability
import ProphetSecretary.Stability.SelectedOccurrence

/-!
# Positive close pairs on actual finite-array branches

Each analytical count branch has the independent finite-instance law. Its
positive tail count is the retained count plus the number of anonymous slots
times one mark-tail probability. No count information is given to a policy.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*}

def hybridClosePositivePair (b η : ℝ) : Set (HybridWorld n Seed) :=
  {v | Model.closePositivePair b η (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2)}

variable [MeasurableSpace Seed]

lemma measurableSet_hybridClosePositivePair (b η : ℝ) :
    MeasurableSet (hybridClosePositivePair b η : Set (HybridWorld n Seed)) := by
  apply measurableSet_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × Model.World n Seed
  have hx (i : Fin n) : Measurable (fun v : Ω => v.2.1 i) := by fun_prop
  have hu (i : Fin n) : Measurable (fun v : Ω => v.2.2.1 i) := by fun_prop
  have hp (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  exact Model.measurableSet_closePositivePair
    (fun k => measurable_combinedValues_family _ hx _ hp k)
    (fun k => measurable_combinedClocks_family _ hu _ hp k) b η

omit [MeasurableSpace Seed] in
lemma appendIID_tailCount (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (N : ℕ) (b : ℝ) :
    (appendIID P κ hκ N).tailCount b=P.tailCount b+(N : ℝ)*κ.real (Ioi b) := by
  unfold Model.Instance.tailCount
  rw [Fin.sum_univ_add]
  simp only [appendIID,Fin.addCases_left,Fin.addCases_right,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rfl

theorem FiniteIntensityHybridInstance.closePositivePair_branch_probability
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (N : ℕ) (b : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    ((arrayLaw B.intensity N).prod (B.individuals.worldLaw ν)).real
      {z : (Fin N → Point) × Model.World n Seed | Model.closePositivePair b η
        (combinedValues z.2.1 z.1) (combinedClocks z.2.2.1 z.1)} ≤
      2*η*(B.individuals.tailCount b+(N : ℝ)*(B.intensity.normalize : Measure ℝ).real (Ioi b))^2 := by
  let κ : Measure ℝ := B.intensity.normalize
  have hκ : ∀ᵐ x ∂κ, 0 ≤ x :=
    (normalized_ae B.intensity hμ B.intensity_supported).mono (fun _ hx => hx.1.le)
  let Q := appendIID B.individuals κ hκ N
  have hMP := finiteArrayWorld_measurePreserving B.individuals κ hκ ν N
  have hE : MeasurableSet {z : Model.World (n+N) Seed | Model.closePositivePair b η z.1 z.2.1} :=
    Model.measurableSet_closePositivePair
      (fun k => (measurable_pi_apply k).comp measurable_fst)
      (fun k => (measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)) b η
  have hReal := congrArg ENNReal.toReal (hMP.measure_preimage hE.nullMeasurableSet)
  change ((arrayLaw B.intensity N).prod (B.individuals.worldLaw ν)).real
      {z : (Fin N → Point) × Model.World n Seed | Model.closePositivePair b η
        (combinedValues z.2.1 z.1) (combinedClocks z.2.2.1 z.1)} =
    (Q.worldLaw ν).real {z : Model.World (n+N) Seed | Model.closePositivePair b η z.1 z.2.1} at hReal
  calc
    _ ≤ 2*η*(Q.tailCount b)^2 := hReal.le.trans (Q.closePositivePair_probability ν b hη)
    _ = _ := by rw [appendIID_tailCount]

end ProphetSecretary.Limiting
