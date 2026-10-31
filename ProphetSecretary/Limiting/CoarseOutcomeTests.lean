import ProphetSecretary.Limiting.HybridFixedCanonicalWeak

/-!
# Bounded continuous coordinate tests for coarse outcomes

Clamping is used only to extend actual cap-bounded reward and unit duration
into globally bounded analytical test functions. On the actual product laws
these tests equal reward and elapsed stopping time, for every admissible
finite policy.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Topology Classical NNReal
namespace ProphetSecretary.Limiting

noncomputable def boundedClamp (H : ℝ≥0) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨(fun x : ℝ => max 0 (min (H:ℝ) x)),by fun_prop⟩ (H:ℝ) (by
    intro x y
    rw [Real.dist_eq]
    change |max 0 (min (H:ℝ) x)-max 0 (min (H:ℝ) y)|≤(H:ℝ)
    apply abs_le.mpr
    constructor
    · have hx0 : 0≤max 0 (min (H:ℝ) x) := le_max_left _ _
      have hyH : max 0 (min (H:ℝ) y)≤(H:ℝ) := max_le H.property (min_le_left _ _)
      linarith
    · have hy0 : 0≤max 0 (min (H:ℝ) y) := le_max_left _ _
      have hxH : max 0 (min (H:ℝ) x)≤(H:ℝ) := max_le H.property (min_le_left _ _)
      linarith)

lemma boundedClamp_bounds (H : ℝ≥0) (x : ℝ) : boundedClamp H x∈Icc (0:ℝ) H :=
  ⟨le_max_left _ _,max_le H.property (min_le_left _ _)⟩

lemma boundedClamp_eq (H : ℝ≥0) {x : ℝ} (hx : x∈Icc (0:ℝ) H) : boundedClamp H x=x := by
  change max 0 (min (H:ℝ) x)=x
  rw [min_eq_right hx.2,max_eq_right hx.1]

noncomputable def coarseRewardTest (n : ℕ) (H : ℝ≥0) : ((ℝ × ℝ) × Model.World n Unit) →ᵇ ℝ :=
  (boundedClamp H).compContinuous ⟨(fun z => z.1.1),by fun_prop⟩

noncomputable def coarseDurationTest (n : ℕ) : ((ℝ × ℝ) × Model.World n Unit) →ᵇ ℝ :=
  (boundedClamp 1).compContinuous ⟨(fun z => z.1.2),by fun_prop⟩

lemma coarseRewardTest_bound (n : ℕ) (H : ℝ≥0) (z : (ℝ × ℝ) × Model.World n Unit) : ‖coarseRewardTest n H z‖≤(H:ℝ) := by
  change ‖boundedClamp H z.1.1‖≤(H:ℝ)
  rw [Real.norm_eq_abs,abs_of_nonneg (boundedClamp_bounds H z.1.1).1]
  exact (boundedClamp_bounds H z.1.1).2

lemma coarseDurationTest_bound (n : ℕ) (z : (ℝ × ℝ) × Model.World n Unit) : ‖coarseDurationTest n z‖≤1 := by
  change ‖boundedClamp 1 z.1.2‖≤1
  rw [Real.norm_eq_abs,abs_of_nonneg (boundedClamp_bounds 1 z.1.2).1]
  exact (boundedClamp_bounds 1 z.1.2).2

lemma finite_policy_outcome_ranges {n : ℕ} (π : Model.RandomizedPolicy n) (P : Model.Instance n) (H : ℝ≥0)
    (hCap : ∀ i, ∀ᵐ x ∂P.law i, x≤(H:ℝ)) :
    ∀ᵐ ω ∂P.worldLaw π.seedLaw, π.realizedReward ω∈Icc (0:ℝ) H ∧ π.realizedDuration ω∈Icc (0:ℝ) 1 := by
  have hValues : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i≤(H:ℝ) :=
    ae_all_iff.mpr (fun i => (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hCap i))
  have hV : MeasurePreserving (fun ω : π.World => ω.1) (P.worldLaw π.seedLaw) P.valuesLaw := measurePreserving_fst
  filter_upwards [hV.quasiMeasurePreserving.ae P.ae_nonnegative,hV.quasiMeasurePreserving.ae hValues,
    P.world_clocks_mem_unitInterval π.seedLaw] with ω h0 hH hU
  exact ⟨⟨π.rule.reward_nonnegative _ _ _ _ h0,
      (π.rule.reward_le_maximum _ _ _ _).trans (Model.Instance.maximum_le _ H.property hH)⟩,
    ⟨π.rule.stoppingTime_nonneg _ _ _ _ (fun i => (hU i).1),π.rule.stoppingTime_le_one _ _ _ _⟩⟩
end ProphetSecretary.Limiting
