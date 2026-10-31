import ProphetSecretary.Model.LawConditionalKernelLimit

/-! # Almost-everywhere regular data for finite law adaptation
Root/clock coincidences are null under every current online law. The initial
endpoint condition is obtained almost everywhere in the perturbation parameter;
no non-atomic offer assumption is made.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

lemma Instance.all_lawStateRoots_ne_clocks_ae (P : Instance n) {w c H : ℝ}
    (_hw : 0 < w) (hc : 0 < c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) (θ : ℝ) :
    ∀ᵐ ω : World n Unit ∂(P.likelihoodWidePath h hh hb hm θ).worldLaw (Measure.dirac ()),
      ∀ (i : Fin n) (A : Finset (Fin n)) (j : Fin n),
        1 - P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i) / c ≠ ω.2.1 j := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  filter_upwards [Q.all_crossingTimes_ne_clocks_ae hQ (Measure.dirac ()) (c / w)] with ω hω
  intro i A j
  have he : 1 - P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i) / c =
      (Q.restrictTo A).crossingTime (Q.restrictTo_integrable_maximum A hQ) (c / w) (ω.1 i) := by
    rw [P.lawStateRoot_eq_instanceRoot hbound h hh hb hm w θ A (ω.1 i)]
    unfold Instance.crossingTime
    field_simp
    rfl
  rw [he]
  exact hω i A j

theorem Instance.lawConditionalRegret_kernel_limit_ae (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-(1 / 4) : ℝ) (1 / 4)),
      ∀ᵐ ω : World n Unit ∂(P.likelihoodWidePath h hh hb hm θ).worldLaw (Measure.dirac ()),
        ∀ i : Fin n, Tendsto (fun δ : ℝ ↦ P.lawConditionalRegret hw hc.le hbound h hh hb hm θ (θ + δ) i ω / δ ^ 2)
          (𝓝[≠] 0) (𝓝 ((∑ A : Finset (Fin n), P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω) / 2)) := by
  filter_upwards [P.all_initial_levels_derivative_zero_ae (Measure.dirac ()) hw.le hc.le hH hbound h hh hb hm,
    ae_restrict_mem measurableSet_Ioo] with θ hInitial hθ
  have hθhalf : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := by constructor <;> linarith [hθ.1, hθ.2]
  let Q := P.likelihoodWidePath h hh hb hm θ
  have hQB := P.likelihoodWidePath_bounded h hh hb hm θ hbound
  filter_upwards [hInitial, Q.world_values_mem_Icc_ae (Measure.dirac ()) hQB,
    Q.world_clocks_lt_one_ae (Measure.dirac ()), P.all_lawStateRoots_ne_clocks_ae hw hc hbound h hh hb hm θ] with ω hI hx hC hN
  intro i
  exact P.lawConditionalRegret_kernel_limit hw hc hH hbound h hh hb hm hθhalf i ω (hx i).1 (hx i).2 hC
    (fun A j _ ↦ hN i A j) (hI i)

end ProphetSecretary.Model
