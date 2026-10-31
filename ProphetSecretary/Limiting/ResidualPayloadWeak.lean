import ProphetSecretary.Limiting.ResidualPayloadDecomposition
import ProphetSecretary.Limiting.WeakRandomizedMarkMap

/-!
# Weak limits of the actual positive residual payload measures

A cofinal residual prefix is eventually beyond each fixed retained prefix.
The old affected upper measure is then genuinely dominated by the coarse
residual. Positive subtraction and the actual weak kernel theorem identify
both the original-sequence limit and the subsequent prefix limit.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
variable {T : Type*} [MeasurableSpace T]

private lemma positiveFiniteDifference_tendsto_eventually {Γ : Type*} {l : Filter Γ}
    {νs μs : Γ → FiniteMeasure ℝ} {ν μ : FiniteMeasure ℝ}
    (hOrders : ∀ᶠ m in l, (μs m : Measure ℝ)≤(νs m : Measure ℝ))
    (hOrder : (μ : Measure ℝ)≤(ν : Measure ℝ))
    (hν : Tendsto νs l (𝓝 ν)) (hμ : Tendsto μs l (𝓝 μ)) :
    Tendsto (fun m => positiveFiniteDifference (νs m) (μs m)) l (𝓝 (positiveFiniteDifference ν μ)) := by
  let νs' := fun m => if (μs m : Measure ℝ)≤(νs m : Measure ℝ) then νs m else μs m
  have hEq : νs'=ᶠ[l]νs := hOrders.mono (fun m hm => if_pos hm)
  have hν' : Tendsto νs' l (𝓝 ν) := hν.congr' hEq.symm
  have hOrder' (m : Γ) : (μs m : Measure ℝ)≤(νs' m : Measure ℝ) := by
    dsimp only [νs']
    split_ifs with hm
    · exact hm
    · exact le_rfl
  have h := positiveFiniteDifference_tendsto hOrder' hOrder hν' hμ
  apply h.congr'
  filter_upwards [hOrders] with m hm
  dsimp only [νs']
  rw [if_pos hm]

lemma residualPayloadBase_tendsto {sizes : ℕ → ℕ} (P : ∀ m, Model.Instance (sizes m))
    (N : ℕ) (Ms : ℕ → ℕ) (hMs : Tendsto Ms atTop atTop)
    {c b : ℝ} (hcb : c≤b) {ρ μ : FiniteMeasure ℝ}
    (hρ : Tendsto (fun m => labeledBandResidual (P m) N c) atTop (𝓝 ρ))
    (hμ : Tendsto (fun m => labeledBandResidual (P m) (Ms m) b) atTop (𝓝 μ))
    (hOrder : (μ : Measure ℝ)≤(ρ : Measure ℝ)) :
    Tendsto (fun m => residualPayloadBase (P m) N (Ms m) c b) atTop
      (𝓝 (positiveFiniteDifference ρ μ)) := by
  have hOrders : ∀ᶠ m in atTop,
      (labeledBandResidual (P m) (Ms m) b : Measure ℝ)≤(labeledBandResidual (P m) N c : Measure ℝ) := by
    filter_upwards [hMs (eventually_ge_atTop N)] with m hm
    rw [← residualPayloadBase_add_old (P m) hm hcb,FiniteMeasure.toMeasure_add]
    apply Measure.le_iff.mpr
    intro E _hE
    rw [Measure.add_apply]
    exact le_add_of_nonneg_left bot_le
  have h := positiveFiniteDifference_tendsto_eventually hOrders hOrder hρ hμ
  apply h.congr'
  filter_upwards [hMs (eventually_ge_atTop N)] with m hm
  exact (residualPayloadBase_eq_difference (P m) hm hcb).symm

lemma positiveFiniteDifference_add_left (A B μ : FiniteMeasure ℝ)
    (hOrder : (μ : Measure ℝ)≤(B : Measure ℝ)) :
    positiveFiniteDifference (A+B) μ=A+positiveFiniteDifference B μ := by
  have hOrder' : (μ : Measure ℝ)≤((A+B : FiniteMeasure ℝ) : Measure ℝ) := by
    apply hOrder.trans
    rw [FiniteMeasure.toMeasure_add]
    apply Measure.le_iff.mpr
    intro E _hE
    rw [Measure.add_apply]
    exact le_add_of_nonneg_left bot_le
  have hL := positiveFiniteDifference_add (A+B) μ hOrder'
  have hR : (A+positiveFiniteDifference B μ)+μ=A+B := by
    rw [add_assoc,positiveFiniteDifference_add B μ hOrder]
  have h := congrArg FiniteMeasure.toMeasure (hL.trans hR.symm)
  rw [FiniteMeasure.toMeasure_add,FiniteMeasure.toMeasure_add] at h
  exact FiniteMeasure.toMeasure_injective ((Measure.add_left_inj _ _ _).mp h)

noncomputable def residualPayloadLimit (ρ : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (κ : Measure T) [IsProbabilityMeasure κ] (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) (N : ℕ) : FiniteMeasure ℝ :=
  positiveFiniteDifference (ρ N) μ+displayedPayloadIntensity μ κ Φ hΦ

lemma residualPayloadLimit_successor (ρ : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (Q : ℕ → ProbabilityMeasure ℝ) (c : ℝ)
    (hSucc : ∀ N, ρ N=(Q N).toFiniteMeasure.restrict (Ioi c)+ρ (N+1))
    (hOrder : ∀ N, (μ : Measure ℝ)≤(ρ N : Measure ℝ))
    (κ : Measure T) [IsProbabilityMeasure κ] (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) (N : ℕ) :
    residualPayloadLimit ρ μ κ Φ hΦ N=(Q N).toFiniteMeasure.restrict (Ioi c)+
      residualPayloadLimit ρ μ κ Φ hΦ (N+1) := by
  unfold residualPayloadLimit
  rw [hSucc N,positiveFiniteDifference_add_left _ _ _ (hOrder (N+1)),add_assoc]

lemma residualPayloadLimit_tendsto {ρ : ℕ → FiniteMeasure ℝ} {μ ν : FiniteMeasure ℝ}
    (hρ : Tendsto ρ atTop (𝓝 ν)) (hOrders : ∀ N, (μ : Measure ℝ)≤(ρ N : Measure ℝ))
    (hOrder : (μ : Measure ℝ)≤(ν : Measure ℝ))
    (κ : Measure T) [IsProbabilityMeasure κ] (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) :
    Tendsto (residualPayloadLimit ρ μ κ Φ hΦ) atTop
      (𝓝 (positiveFiniteDifference ν μ+displayedPayloadIntensity μ κ Φ hΦ)) :=
  (positiveFiniteDifference_tendsto hOrders hOrder hρ tendsto_const_nhds).add_const _

end ProphetSecretary.Limiting
