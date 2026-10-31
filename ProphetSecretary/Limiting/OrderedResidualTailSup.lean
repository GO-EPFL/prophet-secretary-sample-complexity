import ProphetSecretary.Limiting.OrderedBandConvergence

/-!
# The largest residual tail probability tends to zero

The supremum is a deterministic analytical function of the marginal laws.
It bounds every residual coordinate on every array index, lies in the unit
interval, and vanishes under the proved uniform-rarity property.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical
namespace ProphetSecretary.Limiting

noncomputable def residualTailSup (Q : ℕ → ProbabilityMeasure ℝ) (N : ℕ) (d : ℝ) : ℝ :=
  sSup ((fun i => (Q i:Measure ℝ).real (Ioi d)) '' Ici N)

private lemma residualTailSup_bdd (Q : ℕ → ProbabilityMeasure ℝ) (N : ℕ) (d : ℝ) :
    BddAbove ((fun i => (Q i:Measure ℝ).real (Ioi d)) '' Ici N) := by
  refine ⟨1,?_⟩
  rintro _ ⟨i,_hi,rfl⟩
  exact measureReal_le_one

lemma residualTailSup_nonneg (Q : ℕ → ProbabilityMeasure ℝ) (N : ℕ) (d : ℝ) : 0 ≤ residualTailSup Q N d :=
  (show 0 ≤ (Q N:Measure ℝ).real (Ioi d) from measureReal_nonneg).trans
    (le_csSup (residualTailSup_bdd Q N d) ⟨N,le_refl N,rfl⟩)

lemma residualTailSup_le (Q : ℕ → ProbabilityMeasure ℝ) (N : ℕ) (d E : ℝ)
    (h : ∀ i, N ≤ i → (Q i:Measure ℝ).real (Ioi d) ≤ E) : residualTailSup Q N d ≤ E := by
  unfold residualTailSup
  apply csSup_le (s := ((fun i => (Q i:Measure ℝ).real (Ioi d)) '' Ici N))
    ⟨(Q N:Measure ℝ).real (Ioi d),⟨N,le_refl N,rfl⟩⟩
  rintro _ ⟨i,hi,rfl⟩
  exact h i hi

lemma residualTailSup_le_one (Q : ℕ → ProbabilityMeasure ℝ) (N : ℕ) (d : ℝ) : residualTailSup Q N d ≤ 1 :=
  residualTailSup_le Q N d 1 (fun _ _ => measureReal_le_one)

lemma tail_le_residualTailSup (Q : ℕ → ProbabilityMeasure ℝ) (N : ℕ) (d : ℝ) (i : ℕ) (hi : N ≤ i) :
    (Q i:Measure ℝ).real (Ioi d) ≤ residualTailSup Q N d :=
  le_csSup (residualTailSup_bdd Q N d) ⟨i,hi,rfl⟩

lemma residualTailSup_tendsto_zero (Q : ℕ → ℕ → ProbabilityMeasure ℝ) (Ns : ℕ → ℕ) (d : ℝ)
    (hRare : ∀ ε > 0, ∀ᶠ m in atTop, ∀ i, Ns m  ≤  i → (Q m i:Measure ℝ).real (Ioi d)<ε) :
    Tendsto (fun m => residualTailSup (Q m) (Ns m) d) atTop (𝓝 (0:ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hRare (ε/2) (by positivity)] with m hm
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (residualTailSup_nonneg _ _ _)]
  exact (residualTailSup_le (Q m) (Ns m) d (ε/2) (fun i hi => (hm i hi).le)).trans_lt (by linarith)

lemma OrderedBandConvergence.residualTailSup_tendsto_zero
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (d : ℝ) (hd : (B.terminal:ℝ)<d) :
    Tendsto (fun m => residualTailSup (fun i => weightOrderedPaddedLaw (P m) wgt i) (Ns m) d)
      atTop (𝓝 (0:ℝ)) := by
  apply ProphetSecretary.Limiting.residualTailSup_tendsto_zero
  intro ε hε
  obtain ⟨N,hN⟩ := h.uniformly_rare d hd ε hε
  filter_upwards [hNs (eventually_ge_atTop N)] with m hm
  intro i hi
  exact hN m i (hm.trans hi)
end ProphetSecretary.Limiting
