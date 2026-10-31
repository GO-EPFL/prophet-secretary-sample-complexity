import ProphetSecretary.Limiting.TaggedHybridCoefficientStability
import ProphetSecretary.Analysis.StableEnvelope
import ProphetSecretary.Limiting.TaggedHybridIgnoreTags

/-!
# Uniform finite-hybrid envelopes for tagged Poisson value displacements

The common affine representation and selected-occurrence stability give an
explicit remainder uniform in retained dimension and total intensity. The
base optimizer is the verified actual-continuation policy; no varying
optimizer is differentiated.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
open CountableInstance
variable {T : Type} [MeasurableSpace T] [StandardBorelSpace T]

theorem finite_hybrid_poisson_payload_envelope {α : Type*} (n : α → ℕ)
    (B : ∀ a, FiniteIntensityHybridInstance (n a)) {H w c D b : ℝ}
    (hH : 0≤H) (hw : 0<w) (hc : 0<c) (hD : 0≤D) (hb : 0<b)
    (ha : ∀ a, (B a).terminal=0) (hCap : ∀ a, ((B a).cap : ℝ)≤H)
    (L : ℝ → ℝ) (hL : ∀ d, 0<d → 0≤L d)
    (hTail : ∀ a d, 0<d → (B a).tailCount d≤L d) :
    ∃ ψ : ℝ → ℝ, (∀ t, 0≤ψ t) ∧ Monotone ψ ∧ ψ 0=0 ∧
      Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ (κ : Measure T) [IsProbabilityMeasure κ] (_t0 : T)
        (A : ℝ × T → ℝ) (hA : Measurable A) (hABound : ∀ z, |A z|≤D)
        (hVanish : ∀ z, z.1<b → A z=0) a θ, |θ|≤ individualValueRadius D b →
        |((B a).poissonPayloadValuePath κ A hA D b hD hb hABound hVanish θ).optimalScalarValue w c-
          (B a).optimalScalarValue w c-θ*(w*canonicalChronologicalAmplitudeMean (B a) κ A w c)|≤
          (w*ψ (2*(w*D)*|θ|))*|θ| := by
  obtain ⟨ψ,hψ,hMono,hZero,hLim,hCoefficient⟩ :=
    tagged_hybrid_coefficient_stability (T := T) n B hH hw hc hD hb ha hCap L hL hTail
  refine ⟨ψ,hψ,hMono,hZero,hLim,?_⟩
  intro κ _ t0 A hA hABound hVanish a θ hθ
  let P := B a
  let π₀ := (P.valueThresholdPolicy hw.le hc.le).observePayload (Prod.fst : ℝ × T → ℝ) measurable_fst
  let J := fun t (π : RandomizedTaggedHybridPolicy (n a) T) =>
    (π.sampleTags κ).scalarObjective P w c+t*(w*π.payloadAmplitudeMean P κ t0 A)
  let dJ := fun π : RandomizedTaggedHybridPolicy (n a) T => w*π.payloadAmplitudeMean P κ t0 A
  have hOpt : (π₀.sampleTags κ).scalarObjective P w c=P.optimalScalarValue w c :=
    ((P.valueThresholdPolicy hw.le hc.le).observePayload_fst_scalarObjective P (ha a) κ w c).trans
      (P.valueThresholdPolicy_optimal (ha a) hw hc.le)
  have hCoeff₀ : π₀.payloadAmplitudeMean P κ t0 A=canonicalChronologicalAmplitudeMean P κ A w c := by
    have h := hCoefficient κ t0 A hA hABound hVanish a π₀
    rw [hOpt,sub_self,hZero] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  have hbase (π : RandomizedTaggedHybridPolicy (n a) T) : J 0 π≤J 0 π₀ := by
    dsimp only [J]
    rw [zero_mul,add_zero,zero_mul,add_zero,hOpt]
    exact P.scalarObjective_le_value _ w c
  have hDJs (π : RandomizedTaggedHybridPolicy (n a) T) : |dJ π|≤w*D := by
    dsimp only [dJ]
    rw [abs_mul,abs_of_pos hw]
    exact mul_le_mul_of_nonneg_left (π.payloadAmplitudeMean_abs_le P κ t0 A hD hABound) hw.le
  have hStable (π : RandomizedTaggedHybridPolicy (n a) T)
      (hr : J 0 π₀-J 0 π≤2*(w*D)*|θ|) :
      |dJ π-dJ π₀|≤w*ψ (2*(w*D)*|θ|) := by
    have h := hCoefficient κ t0 A hA hABound hVanish a π
    have hr' : P.optimalScalarValue w c-(π.sampleTags κ).scalarObjective P w c≤2*(w*D)*|θ| := by
      simpa only [J,zero_mul,add_zero,hOpt] using hr
    dsimp only [dJ]
    rw [hCoeff₀,← mul_sub,abs_mul,abs_of_pos hw]
    exact mul_le_mul_of_nonneg_left (h.trans (hMono hr')) hw.le
  have hError := ProphetSecretary.Analysis.stable_envelope_error J dJ π₀
    (A := 0) (B := w*D) (θ := θ) (ε := w*ψ (2*(w*D)*|θ|))
    (η := 2*(w*D)*|θ|) (mul_nonneg hw.le (hψ _)) hbase hDJs
    (fun π => by dsimp [J,dJ]; ring_nf; simp only [abs_zero,le_refl]) hStable le_rfl
  have hSup := P.poissonPayloadValuePath_value_eq_sSup (ha a) κ t0 A hA hD hb hABound hVanish hθ w c
  change |sSup (range (J θ))-J 0 π₀-θ*dJ π₀|≤_ at hError
  dsimp only [J,dJ] at hError
  rw [zero_mul,add_zero,hOpt,hCoeff₀] at hError
  simpa only [zero_mul,add_zero,← hSup] using hError

end ProphetSecretary.Limiting
