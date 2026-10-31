import ProphetSecretary.Limiting.LabeledRemainderBand
import ProphetSecretary.Limiting.WeakMeasureOrder

/-!
# Positive residual limits follow from structural body convergence

Mass and support bounds come from actual aggregate marginal restrictions.
The finite residuals decrease when more identities are retained; closedness
of weak measure order passes this to the fixed-prefix limits and then to
the final Poisson intensity. No domination is an additional body field.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma labeledBandResidual_mass_le_tailCount (P : Model.Instance n) (N : ℕ) (b : ℝ) :
    ((labeledBandResidual P N b).mass : ℝ)≤P.tailCount b := by
  change ((labeledBandResidual P N b : Measure ℝ) univ).toReal≤_
  unfold labeledBandResidual
  rw [FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply,
    ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
  simp only [FiniteMeasure.restrict_measure_eq,Measure.restrict_apply_univ]
  change (∑ i∈Finset.univ.filter (fun i : Fin n => N≤ i.val), (P.law i).real (Ioi b))≤_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => measureReal_nonneg)

lemma labeledBandResidual_supported (P : Model.Instance n) (N : ℕ) (b H : ℝ)
    (hCap : ∀ i, ∀ᵐ x ∂P.law i, x≤H) :
    ∀ᵐ x ∂(labeledBandResidual P N b : Measure ℝ), x∈Icc b H := by
  unfold labeledBandResidual
  rw [FiniteMeasure.toMeasure_sum,ae_finsetSum_measure_iff]
  intro i _
  change ∀ᵐ x ∂(P.law i).restrict (Ioi b), x∈Icc b H
  filter_upwards [ae_restrict_mem measurableSet_Ioi,ae_restrict_of_ae (hCap i)] with x hx hH
  exact ⟨hx.le,hH⟩

lemma labeledBandResidual_antitone (P : Model.Instance n) (b : ℝ) {N M : ℕ} (hNM : N≤M) :
    (labeledBandResidual P M b : Measure ℝ)≤(labeledBandResidual P N b : Measure ℝ) := by
  apply Measure.le_iff.mpr
  intro S hS
  unfold labeledBandResidual
  rw [FiniteMeasure.toMeasure_sum,FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply,Measure.finsetSum_apply]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hi'.1,hNM.trans hi'.2⟩
  · intro _ _ _
    exact bot_le

private lemma weak_interval_mass_closed (C : ℝ≥0) {l r : ℝ}
    {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hMass : ∀ m, (μs m).mass≤C)
    (hCap : ∀ m, (μs m : Measure ℝ) (Icc l r)ᶜ=0)
    (hWeak : Tendsto μs atTop (𝓝 μ)) :
    μ.mass≤C ∧ (μ : Measure ℝ) (Icc l r)ᶜ=0 := by
  have hClosed := (isCompact_setOf_finiteMeasure_le_of_isCompact (E := ℝ) C
    (isCompact_Icc : IsCompact (Icc l r))).isClosed
  have hMem := hClosed.mem_of_tendsto hWeak
    (Eventually.of_forall (fun m => ⟨hMass m,(FiniteMeasure.null_iff_toMeasure_null (μs m) _).mpr (hCap m)⟩))
  exact ⟨hMem.1,(FiniteMeasure.null_iff_toMeasure_null μ _).mp hMem.2⟩

theorem LabeledBandConvergence.residual_data {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)}
    {B : CountableInstance} (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ))
    (b : ℝ) (hb : (B.terminal : ℝ)<b)
    (hQatom : ∀ i, (B.individuals i : Measure ℝ) {b}=0) (hμatom : B.intensity {b}=0) :
    ∃ μs : ℕ → FiniteMeasure ℝ,
      (∀ N, Tendsto (fun m => labeledBandResidual (P m) N b) atTop (𝓝 (μs N))) ∧
      Tendsto μs atTop (𝓝 (B.intensityAbove b hb)) ∧
      (∀ N, ∀ᵐ x ∂(μs N : Measure ℝ), x∈Ioc (0 : ℝ) B.cap) ∧
      ∀ N, (B.intensityAbove b hb : Measure ℝ)≤(μs N : Measure ℝ) := by
  obtain ⟨μs,hFirst,hSecond⟩ := h.residual_bands b hb hQatom hμatom
  obtain ⟨K,hK,hBound⟩ := h.above_reserve b hb
  let C : ℝ≥0 := ⟨K,hK⟩
  have hb0 : 0<b := B.terminal.property.trans_lt hb
  have hMass (N m : ℕ) : (labeledBandResidual (P m) N b).mass≤C := by
    change ((labeledBandResidual (P m) N b).mass : ℝ)≤K
    exact (labeledBandResidual_mass_le_tailCount (P m) N b).trans (hBound m)
  have hBandCap (N m : ℕ) : (labeledBandResidual (P m) N b : Measure ℝ) (Icc b (B.cap : ℝ))ᶜ=0 :=
    ae_iff.mp (labeledBandResidual_supported (P m) N b B.cap (hCap m))
  have hLimitCap (N : ℕ) : (μs N).mass≤C ∧ (μs N : Measure ℝ) (Icc b (B.cap : ℝ))ᶜ=0 :=
    weak_interval_mass_closed C (hMass N) (hBandCap N) (hFirst N)
  have hPositive (N : ℕ) : ∀ᵐ x ∂(μs N : Measure ℝ), x∈Ioc (0 : ℝ) B.cap :=
    (ae_iff.mpr (hLimitCap N).2).mono (fun _ hx => ⟨hb0.trans_le hx.1,hx.2⟩)
  have hRawCap (N m : ℕ) : (labeledBandResidual (P m) N b : Measure ℝ) (Icc (0 : ℝ) B.cap)ᶜ=0 :=
    ae_iff.mp ((labeledBandResidual_supported (P m) N b B.cap (hCap m)).mono
      (fun _ hx => ⟨hb0.le.trans hx.1,hx.2⟩))
  have hLimitOrder {N M : ℕ} (hNM : N≤M) : (μs M : Measure ℝ)≤(μs N : Measure ℝ) :=
    weak_measure_order_closed B.cap.property C (hMass N) (hRawCap N)
      (fun m => labeledBandResidual_antitone (P m) b hNM) (hFirst M) (hFirst N)
  refine ⟨μs,hFirst,hSecond,hPositive,?_⟩
  intro N
  have hShift : Tendsto (fun m : ℕ => N+m) atTop atTop :=
    (show StrictMono (fun m : ℕ => N+m) from fun _ _ hm => Nat.add_lt_add_left hm N).tendsto_atTop
  exact weak_measure_order_closed B.cap.property (μs N).mass (fun _ => le_rfl)
    (fun _ => ae_iff.mp ((hPositive N).mono (fun _ hx => ⟨hx.1.le,hx.2⟩)))
    (fun m => hLimitOrder (Nat.le_add_right N m)) (hSecond.comp hShift) tendsto_const_nhds

end ProphetSecretary.Limiting
