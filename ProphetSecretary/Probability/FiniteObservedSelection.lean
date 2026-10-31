import Mathlib.MeasureTheory.Integral.Prod

/-!
# Expectation of a finitely selected response with fresh inputs

Each fixed response has an actual past/future product-law map. A measurable
choice made from past data therefore averages the response's genuine expected
value with the observed choice probability. The product-law premises are
instantiated by actual training/seed projections in ResponseTrainingSplit.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Probability
variable {ι Ω A : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace Ω] [MeasurableSpace A]
    {B : ι → Type*} [∀ c, MeasurableSpace (B c)]

noncomputable def finiteSelectedValue (s : A → ι) (Y : Ω → A) (X : (c : ι) → Ω → B c)
    (f : (c : ι) → B c → ℝ) (ω : Ω) : ℝ := f (s (Y ω)) (X (s (Y ω)) ω)

theorem finiteSelectedValue_integrable_and_integral (ρ : Measure Ω) (μ : Measure A) (ν : (c : ι) → Measure (B c))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [∀ c, IsProbabilityMeasure (ν c)]
    {Y : Ω → A} {X : (c : ι) → Ω → B c} (hPair : ∀ c, MeasurePreserving (fun ω => (Y ω,X c ω)) ρ (μ.prod (ν c)))
    {s : A → ι} (hs : Measurable s) {f : (c : ι) → B c → ℝ}
    (hf : ∀ c, Measurable (f c)) (hfI : ∀ c, Integrable (f c) (ν c)) :
    Integrable (finiteSelectedValue s Y X f) ρ ∧
    (∫ ω, finiteSelectedValue s Y X f ω ∂ρ)=
      ∑ c, μ.real {a | s a=c}*(∫ b, f c b ∂ν c) := by
  have hY : Measurable Y := by
    by_cases hι : Nonempty ι
    · let c := Classical.choice hι
      exact measurable_fst.comp (hPair c).measurable
    · intro t _
      convert (MeasurableSet.empty : MeasurableSet (∅ : Set Ω)) using 1
      ext ω
      exact (hι ⟨s (Y ω)⟩).elim
  let E := fun c => {ω | s (Y ω)=c}
  have hE (c : ι) : MeasurableSet (E c) := measurableSet_eq_fun (hs.comp hY) measurable_const
  let H := fun c => (E c).indicator (fun ω => f c (X c ω))
  have hHI (c : ι) : Integrable (H c) ρ :=
    ((measurePreserving_snd.comp (hPair c)).integrable_comp_of_integrable (hfI c)).indicator (hE c)
  have hSum : finiteSelectedValue s Y X f=∑ c, H c := by
    funext ω
    simp only [Finset.sum_apply,H,Set.indicator_apply,E,Set.mem_setOf_eq,Finset.sum_ite_eq,Finset.mem_univ,if_true,finiteSelectedValue]
  have hInt : Integrable (finiteSelectedValue s Y X f) ρ := by
    rw [hSum]
    have hIntSum : Integrable (fun ω => ∑ c, H c ω) ρ := integrable_finsetSum Finset.univ (fun c _ => hHI c)
    exact hIntSum.congr (Eventually.of_forall fun ω => by simp only [Finset.sum_apply])
  refine ⟨hInt,?_⟩
  rw [hSum]
  simp only [Finset.sum_apply]
  rw [integral_finsetSum _ (fun c _ => hHI c)]
  apply Finset.sum_congr rfl
  intro c _
  let G : A × B c → ℝ := fun p => if s p.1=c then f c p.2 else 0
  have hS : MeasurableSet {a | s a=c} := measurableSet_eq_fun hs measurable_const
  have hGc : MeasurableSet {p : A × B c | s p.1=c} := measurableSet_eq_fun (hs.comp measurable_fst) measurable_const
  have hGm : Measurable G := ((hf c).comp measurable_snd).ite hGc measurable_const
  have hGI : Integrable G (μ.prod (ν c)) := ((hfI c).comp_snd μ).indicator hGc
  have hMap := integral_map (μ:=ρ) (hPair c).measurable.aemeasurable hGm.aestronglyMeasurable
  rw [(hPair c).map_eq] at hMap
  have hH : (∫ ω, H c ω ∂ρ)=∫ p, G p ∂μ.prod (ν c) := by
    apply Eq.trans _ hMap.symm
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by simp only [H,G,E,Set.indicator_apply,Set.mem_setOf_eq]
  rw [hH,integral_prod _ hGI]
  have hInner (a : A) : (∫ b, G (a,b) ∂ν c)=({a | s a=c}.indicator (fun _ => ∫ b, f c b ∂ν c)) a := by
    by_cases ha : s a=c <;> simp only [G,ha,if_true,if_false,Set.indicator_apply,Set.mem_setOf_eq,integral_zero]
  simp_rw [hInner]
  simpa only [smul_eq_mul] using integral_indicator_const (∫ b, f c b ∂ν c) hS

end ProphetSecretary.Probability
