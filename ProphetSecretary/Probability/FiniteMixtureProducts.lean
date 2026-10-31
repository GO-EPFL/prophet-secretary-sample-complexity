import ProphetSecretary.Probability.ConditionalTesting
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Conditioning an actual finite mixture of independent product experiments

The hidden finite atom chooses a past-data law and an independent future law.
All independence is supplied by the constructed product measures. Fubini and
conditional-expectation uniqueness identify the future conditional projection.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Probability
variable {Θ A B : Type*} [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    [MeasurableSpace A] [MeasurableSpace B]

noncomputable def finiteMixtureProductLaw (w : Θ → ℝ≥0) (μ : Θ → Measure A) (ν : Θ → Measure B) :
    Measure (Θ × (A × B)) := ∑ θ, w θ • (Measure.dirac θ).prod ((μ θ).prod (ν θ))

instance finiteMixtureProductLaw_finite (w : Θ → ℝ≥0) (μ : Θ → Measure A) (ν : Θ → Measure B)
    [∀ θ, IsProbabilityMeasure (μ θ)] [∀ θ, IsProbabilityMeasure (ν θ)] :
    IsFiniteMeasure (finiteMixtureProductLaw w μ ν) := by unfold finiteMixtureProductLaw;infer_instance

lemma integrable_of_pointwise_norm_bound {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [IsFiniteMeasure ρ]
    {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, ‖f ω‖≤C) : Integrable f ρ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)

/-- Exact expectation, from the actual finite prior and independent future blocks. -/
theorem integral_finiteMixtureProductLaw (w : Θ → ℝ≥0) (μ : Θ → Measure A) (ν : Θ → Measure B)
    [∀ θ, IsProbabilityMeasure (μ θ)] [∀ θ, IsProbabilityMeasure (ν θ)]
    {f : Θ × (A × B) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, ‖f ω‖≤C) :
    (∫ ω, f ω ∂finiteMixtureProductLaw w μ ν)=
      ∑ θ, (w θ:ℝ)*(∫ a, ∫ b, f (θ,(a,b)) ∂ν θ ∂μ θ) := by
  have hAtom (θ : Θ) : Integrable f ((Measure.dirac θ).prod ((μ θ).prod (ν θ))) :=
    integrable_of_pointwise_norm_bound _ hf hC
  unfold finiteMixtureProductLaw
  rw [integral_finsetSum_measure (fun θ _ => (hAtom θ).smul_measure_nnreal)]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro θ _
  congr 1
  rw [integral_prod _ (hAtom θ),integral_dirac]
  exact integral_prod _ (integrable_of_pointwise_norm_bound ((μ θ).prod (ν θ))
    (hf.comp (measurable_const.prodMk measurable_id)) (fun p => hC (θ,p)))

abbrev mixturePastSigma : MeasurableSpace (Θ × (A × B)) :=
  MeasurableSpace.comap (fun ω : Θ × (A × B) => ω.2.1) inferInstance

omit [Fintype Θ] [MeasurableSingletonClass Θ] in
lemma mixturePastSigma_le : mixturePastSigma (Θ:=Θ) (A:=A) (B:=B) ≤ (inferInstance : MeasurableSpace (Θ × (A × B))) :=
  (measurable_fst.comp measurable_snd).comap_le

/-- Future conditional means that agree separately at every hidden atom and past
observation have the same conditional projection under the actual prior mixture. -/
theorem condExp_finiteMixtureProductLaw_congr (w : Θ → ℝ≥0) (μ : Θ → Measure A) (ν : Θ → Measure B)
    [∀ θ, IsProbabilityMeasure (μ θ)] [∀ θ, IsProbabilityMeasure (ν θ)]
    {f g : Θ × (A × B) → ℝ} (hf : Measurable f) (hg : Measurable g)
    {C : ℝ} (hC0 : 0≤C) (hfC : ∀ ω, ‖f ω‖≤C) (hgC : ∀ ω, ‖g ω‖≤C)
    (hMean : ∀ θ a, (∫ b, f (θ,(a,b)) ∂ν θ)=∫ b, g (θ,(a,b)) ∂ν θ) :
    (finiteMixtureProductLaw w μ ν)[f|mixturePastSigma] =ᵐ[finiteMixtureProductLaw w μ ν]
      (finiteMixtureProductLaw w μ ν)[g|mixturePastSigma] := by
  let ρ := finiteMixtureProductLaw w μ ν
  have hm : mixturePastSigma (Θ:=Θ) (A:=A) (B:=B) ≤ (inferInstance : MeasurableSpace (Θ × (A × B))) := mixturePastSigma_le
  have hfI := integrable_of_pointwise_norm_bound ρ hf hfC
  have hgI := integrable_of_pointwise_norm_bound ρ hg hgC
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hfI (fun _ _ _ => integrable_condExp.integrableOn) ?_
    stronglyMeasurable_condExp.aestronglyMeasurable
  intro E hE _
  rw [setIntegral_condExp hm hgI hE]
  obtain ⟨s,hs,hEeq⟩ := MeasurableSpace.measurableSet_comap.mp hE
  have hEglobal := hm E hE
  rw [←integral_indicator hEglobal,←integral_indicator hEglobal]
  have hIndicatorBound {v : Θ × (A × B) → ℝ} (hv : ∀ ω, ‖v ω‖≤C) :
      ∀ ω, ‖E.indicator v ω‖≤C := by
    intro ω
    by_cases hω : ω∈E
    · simpa only [Set.indicator_of_mem hω] using hv ω
    · simpa only [Set.indicator_of_notMem hω,norm_zero] using hC0
  rw [integral_finiteMixtureProductLaw w μ ν (hg.indicator hEglobal) (hIndicatorBound hgC),
    integral_finiteMixtureProductLaw w μ ν (hf.indicator hEglobal) (hIndicatorBound hfC)]
  apply Finset.sum_congr rfl
  intro θ _
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun a => by
    by_cases ha : a∈s
    · have hMem (b : B) : (θ,(a,b))∈E := by rw [←hEeq];exact ha
      simp only [Set.indicator_of_mem (hMem _)]
      exact (hMean θ a).symm
    · have hMem (b : B) : (θ,(a,b))∉E := by rw [←hEeq];exact ha
      simp only [Set.indicator_of_notMem (hMem _)]

/-- Future block expectation for a fixed candidate atom and already observed past. -/
noncomputable def futureBlockMean (ν : Θ → Measure B) (f : Θ × (A × B) → ℝ)
    (θ : Θ) (ω : Θ × (A × B)) : ℝ := ∫ b, f (θ,(ω.2.1,b)) ∂ν θ

noncomputable def mixtureAtomIndicator (θ : Θ) (ω : Θ × (A × B)) : ℝ := if ω.1=θ then 1 else 0

/-- The actual conditional future law is the mixture of the atomwise independent
future laws with the actual conditional-expectation posterior atom weights. -/
theorem condExp_finiteMixtureProductLaw (w : Θ → ℝ≥0) (μ : Θ → Measure A) (ν : Θ → Measure B)
    [∀ θ, IsProbabilityMeasure (μ θ)] [∀ θ, IsProbabilityMeasure (ν θ)]
    {f : Θ × (A × B) → ℝ} (hf : Measurable f) {C : ℝ} (hC0 : 0≤C) (hfC : ∀ ω, ‖f ω‖≤C) :
    (finiteMixtureProductLaw w μ ν)[f|mixturePastSigma] =ᵐ[finiteMixtureProductLaw w μ ν]
      (fun ω => ∑ θ, futureBlockMean ν f θ ω*
        (finiteMixtureProductLaw w μ ν)[mixtureAtomIndicator θ|mixturePastSigma] ω) := by
  let ρ := finiteMixtureProductLaw w μ ν
  let K := fun θ => futureBlockMean ν f θ
  let I : Θ → (Θ × (A × B)) → ℝ := fun θ => mixtureAtomIndicator (A:=A) (B:=B) θ
  let g : Θ × (A × B) → ℝ := ∑ θ, K θ*I θ
  have hK (θ : Θ) : StronglyMeasurable[mixturePastSigma] (K θ) := by
    have hSect : Measurable (fun p : A × B => f (θ,p)) := hf.comp (measurable_const.prodMk measurable_id)
    have hPast : @Measurable (Θ × (A × B)) A mixturePastSigma _ (fun ω => ω.2.1) :=
      Measurable.of_comap_le le_rfl
    exact hSect.stronglyMeasurable.integral_prod_right'.comp_measurable hPast
  have hKB (θ : Θ) (ω : Θ × (A × B)) : ‖K θ ω‖≤C := by
    change ‖∫ b, f (θ,(ω.2.1,b)) ∂ν θ‖≤C
    simpa only [probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=ν θ) (f:=fun b => f (θ,(ω.2.1,b)))
        (Eventually.of_forall fun b => hfC (θ,(ω.2.1,b)))
  have hIm (θ : Θ) : Measurable (I θ) :=
    (measurable_of_finite (fun t : Θ => if t=θ then (1:ℝ) else 0)).comp measurable_fst
  have hIB (θ : Θ) (ω : Θ × (A × B)) : ‖I θ ω‖≤1 := by
    dsimp [I,mixtureAtomIndicator]
    split_ifs <;> norm_num
  have hII (θ : Θ) : Integrable (I θ) ρ := integrable_of_pointwise_norm_bound ρ (hIm θ) (hIB θ)
  have hProd (θ : Θ) : Integrable (K θ*I θ) ρ := (hII θ).bdd_mul
    ((hK θ).mono mixturePastSigma_le).aestronglyMeasurable (Eventually.of_forall (hKB θ))
  have hg : Measurable g := by
    convert Finset.measurable_sum Finset.univ
      (fun θ _ => ((hK θ).mono mixturePastSigma_le).measurable.mul (hIm θ)) using 1
    funext ω
    simp only [g,Finset.sum_apply]
  have hgPoint (ω : Θ × (A × B)) : g ω=K ω.1 ω := by
    simp only [g,Finset.sum_apply,Pi.mul_apply,I,mixtureAtomIndicator,mul_ite,mul_one,mul_zero,
      Finset.sum_ite_eq,Finset.mem_univ,if_true]
  have hgC (ω : Θ × (A × B)) : ‖g ω‖≤C := by rw [hgPoint];exact hKB _ _
  have hMean (θ : Θ) (a : A) : (∫ b, f (θ,(a,b)) ∂ν θ)=∫ b, g (θ,(a,b)) ∂ν θ := by
    simp_rw [hgPoint]
    simp only [K,futureBlockMean,integral_const,probReal_univ,one_smul]
  have hCE := condExp_finiteMixtureProductLaw_congr w μ ν hf hg hC0 hfC hgC hMean
  have hLin := condExp_finsetSum (μ:=ρ) (s:=Finset.univ) (fun θ _ => hProd θ) mixturePastSigma
  have hPull (θ : Θ) := condExp_mul_of_stronglyMeasurable_left (μ:=ρ) (hK θ) (hProd θ) (hII θ)
  apply hCE.trans
  apply hLin.trans
  have hAll := ae_all_iff.mpr hPull
  filter_upwards [hAll] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun θ _ => hω θ

end ProphetSecretary.Probability
